// Copyright (C) 2022 Lior Stern.
//
// This file is part of liorforth.
// liorforth is free software: you can redistribute it and/or modify it under
// the terms of the GNU General Public License as published by the Free Software
// Foundation, either version 3 of the License, or any later version.
//
// liorforth is distributed in the hope that it will be useful, but WITHOUT ANY
// WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR
// A PARTICULAR PURPOSE. See the GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License along with
// liorforth. If not, see <https://www.gnu.org/licenses/>.

use std::io::Write;
use std::ops::*;

type Cell = isize;

enum Flag {
    False = (0 as Cell),
    True = !(Flag::False as Cell),
}

impl From<bool> for Flag {
    fn from(b: bool) -> Self {
        if b {
            return Flag::True;
        }
        return Flag::False;
    }
}

#[cfg(target_pointer_width = "64")]
type DoubleCell = i128;

#[cfg(target_pointer_width = "32")]
type DoubleCell = i64;

#[cfg(target_pointer_width = "16")]
type DoubleCell = i32;

#[cfg(target_pointer_width = "8")]
type DoubleCell = i16;

type Byte = u8;

type Primitive = fn(&mut Environment);

#[derive(Clone)]
enum ThreadedWordEntry {
    Literal(Cell),
    AnotherWord(*const DictionaryEntry),
    BranchOnFalse(Option<isize /* offset */> /* None for unresolved */),
    Primitive(Primitive),
    Exit,
}

type Word = Vec<ThreadedWordEntry>;

type Name = [Byte; 31];

#[derive(Clone)]
struct DictionaryEntry {
    name: Name,
    immediate: bool,
    execution_body: Word,
    compilation_body: Option<Word>,
}

type Dictionary = std::collections::LinkedList<DictionaryEntry>;

type ReturnStackEntry = *const ThreadedWordEntry;

struct Environment<'a> {
    data_space_pointer: std::slice::IterMut<'a, Byte>,

    data_stack: Vec<Cell>,
    return_stack: Vec<ReturnStackEntry>,

    input_buffer: &'a mut [Byte],
    input_buffer_head: Cell,

    dictionary: Dictionary,

    base: Cell,

    currently_compiling: Cell,
    entry_under_construction: Option<DictionaryEntry>,
    control_flow_stack: Vec<usize>,
}

macro_rules! binary_operator_native_word {
    ($method:tt) => {
        |env| {
            let b = env.data_stack.pop().unwrap();
            let a = env.data_stack.pop().unwrap();
            let c = a.$method(b);
            env.data_stack.push(c);
        }
    };
}

macro_rules! unary_operator_native_word {
    ($operator:tt) => {
	|env| {
            let a = env.data_stack.pop().unwrap();
	    let b = $operator a;
            env.data_stack.push(b);
	}
    }
}

macro_rules! compare_operator_native_word {
    ($operator:tt) => {
	|env| {
            let b = env.data_stack.pop().unwrap();
            let a = env.data_stack.pop().unwrap();
            let c = a $operator b;
	    let f : Flag = c.into();
            env.data_stack.push(f as Cell);
	}
    }
}
const AMOUNT_OF_CELLS_PER_ITEM: usize =
    std::mem::size_of::<ReturnStackEntry>() / std::mem::size_of::<Cell>();

const CONSTANT_PRIMITIVES: &[(&str, Cell)] = &[
    ("true", Flag::True as Cell),
    ("false", Flag::False as Cell),
    ("bl", ' ' as Cell),
    ("nl", '\n' as Cell),
    ("sizeof-cell", std::mem::size_of::<Cell>() as Cell),
    ("sizeof-char", std::mem::size_of::<Byte>() as Cell),
];

const EXECUTION_PRIMITIVES: &[(&str, Primitive)] = &[
    (".s", |env| {
        print!("<{}> ", env.data_stack.len());
        for i in env.data_stack.iter() {
            env.print_number(*i);
        }
    }),
    ("bye", |_env| std::process::exit(0)),
    ("words", |env| {
        // TODO: Implement fmt::Display?
        for entry in env.dictionary.iter() {
            for c in entry.name {
                if c == 0 {
                    break;
                }
                print!("{}", c as char);
            }
            print!("\n");
        }
    }),
    ("dup", |env| {
        let x = *env.data_stack.last().unwrap();
        env.data_stack.push(x)
    }),
    ("drop", |env| {
        env.data_stack.pop().unwrap();
    }),
    (".", |env| {
        let x = env.data_stack.pop().unwrap();
        env.print_number(x);
    }),
    ("swap", |env| {
        let a = env.data_stack.pop().unwrap();
        let b = env.data_stack.pop().unwrap();
        env.data_stack.push(a);
        env.data_stack.push(b);
    }),
    ("over", |env| {
        let a = env.data_stack.pop().unwrap();
        let b = env.data_stack.pop().unwrap();
        env.data_stack.push(b);
        env.data_stack.push(a);
        env.data_stack.push(b);
    }),
    ("nip", |env| {
        let a = env.data_stack.pop().unwrap();
        env.data_stack.pop().unwrap();
        env.data_stack.push(a);
    }),
    ("rot", |env| {
        let a = env.data_stack.pop().unwrap();
        let b = env.data_stack.pop().unwrap();
        let c = env.data_stack.pop().unwrap();
        env.data_stack.push(b);
        env.data_stack.push(a);
        env.data_stack.push(c);
    }),
    ("min", |env| {
        let a = env.data_stack.pop().unwrap();
        let b = env.data_stack.pop().unwrap();
        env.data_stack.push(std::cmp::min(a, b));
    }),
    ("max", |env| {
        let a = env.data_stack.pop().unwrap();
        let b = env.data_stack.pop().unwrap();
        env.data_stack.push(std::cmp::max(a, b));
    }),
    ("abs", |env| {
        let a = env.data_stack.pop().unwrap();
        env.data_stack.push(a.abs());
    }),
    ("/mod", |env| {
        let divisor = env.data_stack.pop().unwrap();
        let divided = env.data_stack.pop().unwrap();
        let remainder = divided % divisor;
        let quotient = divided / divisor; // TODO: Handle 0?
        env.data_stack.push(remainder);
        env.data_stack.push(quotient);
    }),
    ("*/", |env| {
        let n3 = env.data_stack.pop().unwrap();
        let n2 = env.data_stack.pop().unwrap();
        let n1 = env.data_stack.pop().unwrap();

        let double_mul_result: DoubleCell = (n1 as DoubleCell) * (n2 as DoubleCell);
        let double_div_result: DoubleCell = double_mul_result / (n3 as DoubleCell);
        let result: Cell = double_div_result.try_into().unwrap();
        env.data_stack.push(result);
    }),
    ("*/mod", |env| {
        let n3 = env.data_stack.pop().unwrap();
        let n2 = env.data_stack.pop().unwrap();
        let n1 = env.data_stack.pop().unwrap();

        let double_mul_result: DoubleCell = (n1 as DoubleCell) * (n2 as DoubleCell);
        let double_div_result: DoubleCell = double_mul_result / (n3 as DoubleCell);
        let double_mod_result: DoubleCell = double_mul_result % (n3 as DoubleCell);
        let n4: Cell = double_mod_result.try_into().unwrap();
        let n5: Cell = double_div_result.try_into().unwrap();
        env.data_stack.push(n4);
        env.data_stack.push(n5);
    }),
    ("here", |env| {
        let address: *const Byte = env.data_space_pointer.as_ref().as_ptr();
        env.data_stack.push(unsafe { std::mem::transmute(address) });
    }),
    ("allot", |env| {
        let n = env.data_stack.pop().unwrap();
        for _ in 0..n {
            match env.data_space_pointer.next() {
                None => panic!("Not enough memory"),
                _ => {}
            }
        }
    }),
    ("@", |env| {
        let n = env.data_stack.pop().unwrap();
        let address: *mut Cell;
        let data: Cell;
        unsafe {
            address = std::mem::transmute(n);
            data = *address;
        }
        env.data_stack.push(data);
    }),
    ("!", |env| {
        let n = env.data_stack.pop().unwrap();
        let data = env.data_stack.pop().unwrap();
        let address: *mut Cell;
        unsafe {
            address = std::mem::transmute(n);
            *address = data;
        }
    }),
    ("c@", |env| {
        let n = env.data_stack.pop().unwrap();
        let address: *mut Byte;
        let data: Byte;
        unsafe {
            address = std::mem::transmute(n);
            data = *address;
        }
        env.data_stack.push(data as Cell);
    }),
    ("c!", |env| {
        let n = env.data_stack.pop().unwrap();
        let data = env.data_stack.pop().unwrap() as Byte;
        let address: *mut Byte;
        unsafe {
            address = std::mem::transmute(n);
            *address = data;
        }
    }),
    ("emit", |env| {
        let n = env.data_stack.pop().unwrap();
        let c = (n as u8) as char;
        print!("{}", c);
    }),
    ("base", |env| {
        env.data_stack
            .push(unsafe { std::mem::transmute(&env.base) });
    }),
    ("+", binary_operator_native_word!(wrapping_add)),
    ("-", binary_operator_native_word!(wrapping_sub)),
    ("*", binary_operator_native_word!(wrapping_mul)),
    ("and", binary_operator_native_word!(bitand)),
    ("or", binary_operator_native_word!(bitor)),
    ("xor", binary_operator_native_word!(bitxor)),
    ("mod", binary_operator_native_word!(wrapping_rem)),
    ("lshift", binary_operator_native_word!(shl)),
    ("rshift", binary_operator_native_word!(shr)),
    ("negate", unary_operator_native_word!(-)),
    ("invert", unary_operator_native_word!(!)),
    ("=", compare_operator_native_word!(==)),
    ("<", compare_operator_native_word!(<)),
    (">", compare_operator_native_word!(>)),
    (
        // Not a part of the core words, but its useful for debugging
        // TODO: Replace with a threaded word once compilation fully is working
        "dump",
        |env| {
            const ROW_SIZE: usize = 0x10;
            let byte_count: usize = unsafe { std::mem::transmute(env.data_stack.pop().unwrap()) };
            let address: usize = unsafe { std::mem::transmute(env.data_stack.pop().unwrap()) };

            for i in 0..byte_count {
                if i % ROW_SIZE == 0 {
                    print!("{:X}: ", address + i);
                }

                let ptr: *const Byte = unsafe { std::mem::transmute(address + i) };

                print!("{:02X} ", unsafe { *ptr });

                if i % ROW_SIZE == ROW_SIZE - 1 {
                    println!("");
                }
            }

            println!("");
        },
    ),
    (":", |env| {
        if env.entry_under_construction.is_some() {
            panic!("Can't double compile!");
        }

        env.entry_under_construction = Some(DictionaryEntry {
            name: env.read_name_from_input_buffer().unwrap(),
            immediate: false,
            execution_body: Vec::new(),
            compilation_body: None,
        });
        env.currently_compiling = Flag::True as Cell;
    }),
    ("r>", |env| {
        let item = env.return_stack.pop().unwrap();
        let item_as_cells: &[Cell; AMOUNT_OF_CELLS_PER_ITEM] =
            unsafe { std::mem::transmute(&item) };

        for i in item_as_cells {
            env.data_stack.push(*i);
        }
    }),
    (">r", |env| {
        let mut cells_to_create_return_stack_entry = [0 as Cell; AMOUNT_OF_CELLS_PER_ITEM];

        for cell in cells_to_create_return_stack_entry.iter_mut().rev() {
            cell.clone_from(&env.data_stack.pop().unwrap());
        }

        let return_stack_entry: &ReturnStackEntry =
            unsafe { std::mem::transmute(&cells_to_create_return_stack_entry) };

        env.return_stack.push(return_stack_entry.clone());
    }),
    ("r@", |env| {
        let item = env.return_stack.last().unwrap().clone();
        let item_as_cells: &[Cell; AMOUNT_OF_CELLS_PER_ITEM] =
            unsafe { std::mem::transmute(&item) };

        for i in item_as_cells {
            env.data_stack.push(*i);
        }
    }),
    ("fill", |env| {
        let c = env.data_stack.pop().unwrap() as Byte;
        let amount = env.data_stack.pop().unwrap();
        let addr = env.data_stack.pop().unwrap();
        let addr: *mut Byte = unsafe { std::mem::transmute(addr) };
        let range: &mut [Byte] = unsafe { std::slice::from_raw_parts_mut(addr, amount as usize) };
        range.fill(c);
    }),
    ("u.", |env| {
        let s = env.data_stack.pop().unwrap();
        let u: usize = s as usize;
        env.print_number(u);
    }),
    ("u<", |env| {
        let s2 = env.data_stack.pop().unwrap();
        let s1 = env.data_stack.pop().unwrap();
        let u2 = s2 as usize;
        let u1 = s1 as usize;
        let result: bool = u1 < u2;
        let result: Flag = result.into();
        env.data_stack.push(result as Cell);
    }),
    ("move", |env| {
        let length = env.data_stack.pop().unwrap() as usize;

        let dest: *mut Byte = unsafe { std::mem::transmute(env.data_stack.pop().unwrap()) };
        let src: *const Byte = unsafe { std::mem::transmute(env.data_stack.pop().unwrap()) };

        let src: &[Byte] = unsafe { std::slice::from_raw_parts(src, length) };
        let dest: &mut [Byte] = unsafe { std::slice::from_raw_parts_mut(dest, length) };

        dest.copy_from_slice(src);
    }),
    ("depth", |env| {
        env.data_stack.push(env.data_stack.len() as Cell);
    }),
    ("quit", |env| {
        env.return_stack.clear();
        // TODO: Don't print ok after execution
    }),
    (">in", |env| {
        let address: Cell = unsafe { std::mem::transmute(&env.input_buffer_head) };
        env.data_stack.push(address);
    }),
    ("state", |env| {
        let address: Cell = unsafe { std::mem::transmute(&env.currently_compiling) };
        env.data_stack.push(address);
    }),
    ("source", |env| {
        let address: Cell = unsafe { std::mem::transmute(env.input_buffer.as_ptr()) };
        let mut size: Cell = 0;
        loop {
            match env.input_buffer.get(size as usize) {
                Some(c) => {
                    if *c == 0 {
                        break;
                    }
                }
                _ => break,
            }
            size += 1;
        }
        env.data_stack.push(address);
        env.data_stack.push(size);
    }),
    ("immediate", |env| {
        env.dictionary.back_mut().unwrap().immediate = true;
    }),
    ("create", |env| {
        env.align_data_pointer();
        let data = env.data_space_pointer.as_ref().as_ptr();
        let data: Cell = unsafe { std::mem::transmute(data) };

        let name = env.read_name_from_input_buffer().unwrap();
        env.dictionary.push_back(DictionaryEntry {
            name,
            immediate: false,
            execution_body: vec![ThreadedWordEntry::Literal(data), ThreadedWordEntry::Exit],
            compilation_body: None,
        });
    }),
    ("constant", |env| {
        let data = env.data_stack.pop().unwrap();

        let name = env.read_name_from_input_buffer().unwrap();
        env.dictionary.push_back(DictionaryEntry {
            name,
            immediate: true,
            execution_body: vec![ThreadedWordEntry::Literal(data), ThreadedWordEntry::Exit],
            compilation_body: None,
        });
    }),
    ("align", |env| env.align_data_pointer()),
];

const COMPILATION_PRIMITIVES: &[(&str, Primitive)] = &[
    (";", |env| {
        if env.entry_under_construction.is_none() {
            panic!("Using ; without : !");
        }

        let entry_under_construction = env.entry_under_construction.as_mut().unwrap();

        entry_under_construction
            .execution_body
            .push(ThreadedWordEntry::Exit);

        if entry_under_construction.compilation_body.is_some() {
            entry_under_construction
                .compilation_body
                .as_mut()
                .unwrap()
                .push(ThreadedWordEntry::Exit);
        }

        // TODO: Print a message if a word is re-defined
        let new_entry = env.entry_under_construction.clone().unwrap();
        env.dictionary.push_front(new_entry);

        env.entry_under_construction = None;
        env.currently_compiling = Flag::False as Cell;
    }),
    ("if", |env| {
        env.entry_under_construction
            .as_mut()
            .unwrap()
            .execution_body
            .push(ThreadedWordEntry::BranchOnFalse(None));
    }),
    ("else", |env| {
        let unresolved_if_branch_index = env.index_of_last_unresolved_branch().unwrap();
        env.entry_under_construction
            .as_mut()
            .unwrap()
            .execution_body
            .push(ThreadedWordEntry::Literal(Flag::False as Cell));
        env.entry_under_construction
            .as_mut()
            .unwrap()
            .execution_body
            .push(ThreadedWordEntry::BranchOnFalse(None));
        let branch_offset = env
            .entry_under_construction
            .as_ref()
            .unwrap()
            .execution_body
            .len()
            - unresolved_if_branch_index;
        let unresolved_branch: &mut ThreadedWordEntry = env
            .entry_under_construction
            .as_mut()
            .unwrap()
            .execution_body
            .get_mut(unresolved_if_branch_index)
            .unwrap();
        *unresolved_branch = ThreadedWordEntry::BranchOnFalse(Some(branch_offset as isize));
    }),
    ("then", |env| {
        let unresolved_branch_index = env.index_of_last_unresolved_branch().unwrap();
        let branch_offset = env
            .entry_under_construction
            .as_ref()
            .unwrap()
            .execution_body
            .len()
            - unresolved_branch_index;
        let unresolved_branch: &mut ThreadedWordEntry = env
            .entry_under_construction
            .as_mut()
            .unwrap()
            .execution_body
            .get_mut(unresolved_branch_index)
            .unwrap();
        *unresolved_branch = ThreadedWordEntry::BranchOnFalse(Some(branch_offset as isize));
    }),
    ("begin", |env| {
        env.control_flow_stack.push(
            env.entry_under_construction
                .as_ref()
                .unwrap()
                .execution_body
                .len(),
        );
    }),
    ("until", |env| {
        let branch_offset = env
            .entry_under_construction
            .as_ref()
            .unwrap()
            .execution_body
            .len()
            - env.control_flow_stack.pop().unwrap();
        let branch_offset = branch_offset as isize;
        let branch_offset = -branch_offset;
        env.entry_under_construction
            .as_mut()
            .unwrap()
            .execution_body
            .push(ThreadedWordEntry::BranchOnFalse(Some(branch_offset)));
    }),
    ("while", |env| {
        env.entry_under_construction
            .as_mut()
            .unwrap()
            .execution_body
            .push(ThreadedWordEntry::BranchOnFalse(None));
    }),
    ("repeat", |env| {
        let begin_index = env.control_flow_stack.pop().unwrap();
        env.entry_under_construction
            .as_mut()
            .unwrap()
            .execution_body
            .push(ThreadedWordEntry::Literal(Flag::False as Cell));
        let true_jump_offset = env
            .entry_under_construction
            .as_ref()
            .unwrap()
            .execution_body
            .len()
            - begin_index;
        let true_jump_offset = true_jump_offset as isize;
        let true_jump_offset = -true_jump_offset;
        env.entry_under_construction
            .as_mut()
            .unwrap()
            .execution_body
            .push(ThreadedWordEntry::BranchOnFalse(Some(true_jump_offset)));

        let unresolved_while_branch_index = env.index_of_last_unresolved_branch().unwrap();
        let false_jump_offset = env
            .entry_under_construction
            .as_mut()
            .unwrap()
            .execution_body
            .len()
            - unresolved_while_branch_index;
        let false_jump_offset = false_jump_offset as isize;
        let unresolved_branch: &mut ThreadedWordEntry = env
            .entry_under_construction
            .as_mut()
            .unwrap()
            .execution_body
            .get_mut(unresolved_while_branch_index)
            .unwrap();
        *unresolved_branch = ThreadedWordEntry::BranchOnFalse(Some(false_jump_offset));
    }),
    ("exit", |env| {
        env.entry_under_construction
            .as_mut()
            .unwrap()
            .execution_body
            .push(ThreadedWordEntry::Exit);
    }),
    ("literal", |env| {
        let data = env.data_stack.pop().unwrap();
        let literal = ThreadedWordEntry::Literal(data);
        env.entry_under_construction
            .as_mut()
            .unwrap()
            .execution_body
            .push(literal);
    }),
    ("postpone", |env| {
        let name = env.read_name_from_input_buffer().unwrap();
        let entry = search_dictionary(&env.dictionary, &name).unwrap();

        let maybe_compilation_body = &mut env
            .entry_under_construction
            .as_mut()
            .unwrap()
            .compilation_body;
        if maybe_compilation_body.is_none() {
            *maybe_compilation_body = Some(vec![]);
        }
        let compilation_body = maybe_compilation_body.as_mut().unwrap();
        let entry = unsafe { entry.as_ref() }.unwrap();

        if entry.immediate {
            let mut to_append = entry.compilation_body.as_ref().unwrap().clone();
            match to_append.pop() {
                Some(ThreadedWordEntry::Exit) => {}
                _ => panic!("Corrupted word"),
            }
            compilation_body.append(&mut to_append);
        } else {
            compilation_body.push(ThreadedWordEntry::AnotherWord(entry));
        }
    }),
];

// TODO: Implement From?
fn name_from_str(s: &str) -> Option<Name> {
    let mut result = Name::default();

    if s.as_bytes().len() > result.len() {
        return None;
    }

    result[0..s.as_bytes().len()].clone_from_slice(s.as_bytes());
    return Some(result);
}

fn search_dictionary(dict: &Dictionary, name: &Name) -> Option<*const DictionaryEntry> {
    for item in dict {
        if item.name == *name {
            return Some(item.deref());
        }
    }
    return None;
}

fn initial_dictionary() -> Dictionary {
    let constant_entries = CONSTANT_PRIMITIVES
        .iter()
        .map(|(name, value)| DictionaryEntry {
            name: name_from_str(name).unwrap(),
            immediate: true,
            execution_body: vec![ThreadedWordEntry::Literal(*value), ThreadedWordEntry::Exit],
            compilation_body: None,
        });

    let execute_only_entries =
        EXECUTION_PRIMITIVES
            .iter()
            .map(|(name, exec_ptr)| DictionaryEntry {
                name: name_from_str(name).unwrap(),
                immediate: false,
                execution_body: vec![
                    ThreadedWordEntry::Primitive(exec_ptr.clone()),
                    ThreadedWordEntry::Exit,
                ],
                compilation_body: None,
            });

    let compile_only_entries =
        COMPILATION_PRIMITIVES
            .iter()
            .map(|(name, comp_ptr)| DictionaryEntry {
                name: name_from_str(name).unwrap(),
                immediate: false,
                execution_body: vec![
                    ThreadedWordEntry::Primitive(|_env| {
                        panic!("Tried to execute a compile only word!");
                    }),
                    ThreadedWordEntry::Exit,
                ],
                compilation_body: Some(vec![
                    ThreadedWordEntry::Primitive(comp_ptr.clone()),
                    ThreadedWordEntry::Exit,
                ]),
            });

    let entries = constant_entries
        .chain(execute_only_entries)
        .chain(compile_only_entries);

    return std::collections::LinkedList::from_iter(entries);
}

const CORE_WORDS_INIT: &str = include_str!("core.fth");

fn parse_number(default_base: u32, word: &str) -> Option<Cell> {
    if word.is_empty() {
        return None;
    }

    let (base, has_base_indicator) = match word.chars().nth(0).unwrap() {
        '#' => (10, true),
        '$' => (16, true),
        '%' => (2, true),
        _ => (default_base, false),
    };

    let rest = match has_base_indicator {
        true => word.split_at(1).1,
        _ => word,
    };

    return match Cell::from_str_radix(rest, base) {
        Ok(x) => Some(x),
        _ => None,
    };
}

fn append_immidiate(destination: &mut Word, immidate: &Word) {
    let mut to_append = immidate.clone();

    // Remove exit at the end
    match to_append.pop().unwrap() {
        ThreadedWordEntry::Exit => {}
        _ => panic!("Corrupted immediate (no exit found)"),
    }

    destination.append(&mut to_append);
}

impl<'a> Environment<'a> {
    fn new(data_space: &'a mut [Byte], input_buffer: &'a mut [Byte]) -> Environment<'a> {
        let mut env = Environment {
            data_space_pointer: data_space.iter_mut(),
            data_stack: Vec::new(),
            return_stack: Vec::new(),
            input_buffer,
            input_buffer_head: 0,
            dictionary: initial_dictionary(),
            base: 10,
            currently_compiling: Flag::False as Cell,
            entry_under_construction: None,
            control_flow_stack: Vec::new(),
        };

        for line in CORE_WORDS_INIT.lines() {
            // TODO: Remove when "\" is implemented
            if !line.starts_with("\\") {
                env.interpret_line(line);
            }
        }

        return env;
    }

    fn compile_mode(&self) -> bool {
        if self.currently_compiling == Flag::True as Cell {
            assert!(self.entry_under_construction.is_some());
            return true;
        }

        assert!(self.entry_under_construction.is_none());
        return false;
    }

    fn next_token(
        &mut self,
        skip_leading_delimiters: bool,
        delimiter: Byte,
    ) -> (
        usize, /* input buffer offset */
        usize, /* token size */
    ) {
        if skip_leading_delimiters {
            'find_first_char: loop {
                if self.input_buffer_head as usize >= self.input_buffer.len() {
                    return (0, 0);
                }

                if *self
                    .input_buffer
                    .get(self.input_buffer_head as usize)
                    .unwrap()
                    == 0
                {
                    return (0, 0);
                }

                if *self
                    .input_buffer
                    .get(self.input_buffer_head as usize)
                    .unwrap()
                    != delimiter
                {
                    break 'find_first_char;
                }

                self.input_buffer_head += 1;
            }
        }

        let token_begin = self.input_buffer_head as usize;
        let token_size;

        'read_token: loop {
            if self.input_buffer_head as usize >= self.input_buffer.len()
                || *self
                    .input_buffer
                    .get(self.input_buffer_head as usize)
                    .unwrap()
                    == 0
            {
                token_size = (self.input_buffer_head as usize) - token_begin;
                break 'read_token;
            }

            if *self
                .input_buffer
                .get(self.input_buffer_head as usize)
                .unwrap()
                == delimiter
            {
                token_size = (self.input_buffer_head as usize) - token_begin;
                self.input_buffer_head += 1;
                break 'read_token;
            }

            self.input_buffer_head += 1;
        }

        return (token_begin, token_size);
    }

    fn interpret_line(&mut self, line: &str) {
        if line.len() == 0 {
            return;
        }

        self.input_buffer_head = 0;
        self.input_buffer.fill(0);
        for i in 0..line.as_bytes().len() {
            self.input_buffer[i] = *line.as_bytes().get(i).unwrap();
        }

        'empty_input_buffer: loop {
            let (token_begin, token_size) = self.next_token(true, ' ' as Byte);

            if token_size == 0 {
                break 'empty_input_buffer;
            }

            let token: String =
                String::from_utf8_lossy(&self.input_buffer[token_begin..token_begin + token_size])
                    .to_string();

            self.handle_token(&token);
        }
    }

    fn handle_token(&mut self, token: &str) {
        match parse_number(self.base as u32, &token) {
            Some(number) => self.handle_number_token(number),
            _ => self.hanle_text_token(token),
        }
    }

    fn handle_number_token(&mut self, token: Cell) {
        if self.compile_mode() {
            let literal = ThreadedWordEntry::Literal(token);
            self.entry_under_construction
                .as_mut()
                .unwrap()
                .execution_body
                .push(literal);
        } else {
            self.data_stack.push(token);
        }
    }

    fn hanle_text_token(&mut self, token: &str) {
        let name = name_from_str(token).unwrap();
        let dict_entry = search_dictionary(&self.dictionary, &name).unwrap();
        let dict_entry = unsafe { dict_entry.as_ref() }.unwrap();

        if self.compile_mode() {
            match &dict_entry.compilation_body {
                Some(thing_to_execute) => {
                    assert_eq!(dict_entry.immediate, false); // Is that even a thing?
                    self.execute_word(thing_to_execute.first().unwrap());
                }
                _ => {
                    if dict_entry.immediate {
                        append_immidiate(
                            &mut self
                                .entry_under_construction
                                .as_mut()
                                .unwrap()
                                .execution_body,
                            &dict_entry.execution_body,
                        );
                    } else {
                        let another_word = ThreadedWordEntry::AnotherWord(dict_entry);
                        self.entry_under_construction
                            .as_mut()
                            .unwrap()
                            .execution_body
                            .push(another_word);
                    }
                }
            }
        } else {
            let next_word = &dict_entry.execution_body;
            self.execute_word(next_word.first().unwrap());
        }
    }

    fn execute_word(&mut self, entry: &ThreadedWordEntry) {
        let mut instruction_pointer: *const ThreadedWordEntry = entry;
        loop {
            match unsafe { instruction_pointer.as_ref() }.unwrap() {
                ThreadedWordEntry::AnotherWord(w) => {
                    let w = unsafe { w.as_ref() }.unwrap();
                    let to_execute;
                    if self.compile_mode() {
                        to_execute = w.compilation_body.as_ref().unwrap();
                    } else {
                        to_execute = w.execution_body.as_ref();
                    }

                    let next = unsafe { instruction_pointer.add(1) };
                    self.return_stack.push(next);
                    instruction_pointer = to_execute.first().unwrap();
                    continue;
                }
                ThreadedWordEntry::Literal(l) => self.data_stack.push(*l),
                ThreadedWordEntry::BranchOnFalse(offset) => {
                    let cond = self.data_stack.pop().unwrap();
                    if cond == Flag::False as Cell {
                        instruction_pointer =
                            unsafe { instruction_pointer.offset(offset.unwrap()) };
                        continue;
                    }
                }
                ThreadedWordEntry::Primitive(func) => func(self),
                ThreadedWordEntry::Exit => match self.return_stack.pop() {
                    Some(next) => {
                        instruction_pointer = next;
                        continue;
                    }
                    _ => {
                        break; // Nothing left to execute
                    }
                },
            }

            instruction_pointer = unsafe { instruction_pointer.add(1) };
        }
    }

    fn print_number<T: std::fmt::Binary + std::fmt::LowerHex + std::fmt::Display>(&self, n: T) {
        match self.base {
            2 => print!("{:b} ", n),
            16 => print!("{:x} ", n),
            _ => print!("{} ", n),
        }
    }

    fn index_of_last_unresolved_branch(&self) -> Option<usize> {
        let mut index_from_the_end = 0;
        for item in self
            .entry_under_construction
            .as_ref()
            .unwrap()
            .execution_body
            .iter()
            .rev()
        {
            index_from_the_end += 1;
            match item {
                ThreadedWordEntry::BranchOnFalse(b) => match b {
                    None => {
                        return Some(
                            self.entry_under_construction
                                .as_ref()
                                .unwrap()
                                .execution_body
                                .len()
                                - index_from_the_end,
                        );
                    }
                    _ => {}
                },
                _ => {}
            }
        }
        return None;
    }

    fn align_data_pointer(&mut self) {
        loop {
            let data = self.data_space_pointer.as_ref().as_ptr();
            let data: usize = unsafe { std::mem::transmute(data) };
            if data % std::mem::size_of::<Cell>() == 0 {
                break;
            }
            self.data_space_pointer.next().unwrap();
        }
    }

    fn read_name_from_input_buffer(&mut self) -> Option<Name> {
        let (token_offset, token_size) = self.next_token(true, ' ' as Byte);
        if token_size == 0 {
            return None;
        }

        let mut name = Name::default();
        name[0..token_size]
            .copy_from_slice(&self.input_buffer[token_offset..(token_offset + token_size)]);
        return Some(name);
    }
}

fn main() {
    const DATA_SPACE_SIZE: usize = 10 * 1024;
    let mut data_space: [Byte; DATA_SPACE_SIZE] = [0; DATA_SPACE_SIZE];

    const INPUT_BUFFER_SIZE: usize = 1024;
    let mut input_buffer = [0; INPUT_BUFFER_SIZE];

    let mut environment = Environment::new(&mut data_space, &mut input_buffer);
    loop {
        let mut line_buffer = String::new();
        std::io::stdin().read_line(&mut line_buffer).unwrap();
        line_buffer.pop();
        environment.interpret_line(&line_buffer);
        println!(" ok. ");
        std::io::stdout().flush().unwrap();
    }
}

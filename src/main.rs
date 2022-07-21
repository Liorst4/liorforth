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

fn encode_counted_string(src: &[Byte]) -> Vec<Byte> {
    let mut result = src.to_vec();
    result.insert(0, src.len() as Byte);
    return result;
}

unsafe fn decode_counted_string(src: *const Byte) -> (usize, *const Byte) {
    return (*src as usize, src.add(1));
}

type Primitive = fn(&mut Environment);

#[derive(Clone)]
enum ForthOperation {
    PushCellToDataStack(Cell),
    CallAnotherDictionaryEntry(*const DictionaryEntry),

    // TODO: Implement as a primitive
    BranchOnFalse(Option<isize /* offset */> /* None for unresolved */),

    CallPrimitive(Primitive),

    // TODO: Implement as a primitive
    Return,
}

#[derive(Clone)]
struct DictionaryEntry {
    name: String,
    immediate: bool,
    body: Vec<ForthOperation>,
}

type Dictionary = std::collections::LinkedList<DictionaryEntry>;

struct Environment<'a> {
    data_space_pointer: std::slice::IterMut<'a, Byte>,

    data_stack: Vec<Cell>,
    return_stack: Vec<*const ForthOperation>,

    input_buffer: &'a mut [Byte],
    input_buffer_head: Cell,

    dictionary: Dictionary,

    base: Cell,

    currently_compiling: Cell,
    control_flow_stack: Vec<usize>,

    parsed_word: Vec<Byte>,
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
        for entry in env.dictionary.iter() {
            print!("{}\n", entry.name);
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
        let name = env.read_name_from_input_buffer().unwrap();
        env.dictionary.push_front(DictionaryEntry {
            name,
            immediate: false,
            body: Vec::new(),
        });
        env.currently_compiling = Flag::True as Cell;
    }),
    ("r>", |env| {
        let calling_word_return_address = env.return_stack.pop().unwrap();

        let from_return_stack = env.return_stack.pop().unwrap();
        env.data_stack
            .push(unsafe { std::mem::transmute(from_return_stack) });

        env.return_stack.push(calling_word_return_address);
    }),
    (">r", |env| {
        let calling_word_return_address = env.return_stack.pop().unwrap();

        let from_data_stack = env.data_stack.pop().unwrap();
        env.return_stack
            .push(unsafe { std::mem::transmute(from_data_stack) });

        env.return_stack.push(calling_word_return_address);
    }),
    ("r@", |env| {
        let calling_word_return_address = env.return_stack.pop().unwrap();

        let from_return_stack = env.return_stack.last().unwrap().clone();
        env.data_stack
            .push(unsafe { std::mem::transmute(from_return_stack) });

        env.return_stack.push(calling_word_return_address);
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
        env.latest().immediate = true;
    }),
    ("create", |env| {
        env.align_data_pointer();
        let data = env.data_space_pointer.as_ref().as_ptr();
        let data: Cell = unsafe { std::mem::transmute(data) };

        let name = env.read_name_from_input_buffer().unwrap();
        env.dictionary.push_back(DictionaryEntry {
            name,
            immediate: false,
            body: vec![
                ForthOperation::PushCellToDataStack(data),
                ForthOperation::Return,
            ],
        });
    }),
    ("constant", |env| {
        let data = env.data_stack.pop().unwrap();

        let name = env.read_name_from_input_buffer().unwrap();
        env.dictionary.push_back(DictionaryEntry {
            name,
            immediate: false,
            body: vec![
                ForthOperation::PushCellToDataStack(data),
                ForthOperation::Return,
            ],
        });
    }),
    ("align", |env| env.align_data_pointer()),
    ("spaces", |env| {
        let amount = env.data_stack.pop().unwrap();
        if amount > 0 {
            for _ in 0..amount {
                print!(" ");
            }
        }
    }),
    ("char", |env| {
        let (offset, length) = env.next_token(true, ' ' as Byte);
        assert_eq!(length, 1);
        let c = *env.input_buffer.get(offset).unwrap();
        env.data_stack.push(c as Cell);
    }),
    ("word", |env| {
        let delimiter = env.data_stack.pop().unwrap();
        let (offset, length) = env.next_token(true, delimiter as Byte);
        env.parsed_word = encode_counted_string(&env.input_buffer[offset..offset + length]);
        env.data_stack
            .push(unsafe { std::mem::transmute(env.parsed_word.as_ptr()) });
    }),
    ("count", |env| {
        let address = env.data_stack.pop().unwrap();
        let address: *const u8 = unsafe { std::mem::transmute(address) };
        let (count, _) = unsafe { decode_counted_string(address) };
        env.data_stack.push(count as Cell);
    }),
    ("'", |env| {
        let name = env.read_name_from_input_buffer().unwrap();
        let entry = search_dictionary(&env.dictionary, &name).unwrap();
        env.data_stack.push(unsafe { std::mem::transmute(entry) });
    }),
    ("execute", |env| {
        let entry = env.data_stack.pop().unwrap();
        let entry: *const DictionaryEntry = unsafe { std::mem::transmute(entry) };
        let entry = unsafe { entry.as_ref() }.unwrap();
        env.execute_word(entry.body.first().unwrap());
    }),
    (">body", |env| {
        let entry = env.data_stack.pop().unwrap();
        let entry: *const DictionaryEntry = unsafe { std::mem::transmute(entry) };
        let entry = unsafe { entry.as_ref() }.unwrap();
        match entry.body.get(0).unwrap() {
            ForthOperation::PushCellToDataStack(result) => env.data_stack.push(*result),
            _ => panic!("Invalid argument given to >body"),
        }
    }),
    ("find", |env| {
        let name_conuted_string = env.data_stack.pop().unwrap();
        let (name_bytecount, name_begin) =
            unsafe { decode_counted_string(std::mem::transmute(name_conuted_string)) };
        let name = unsafe { std::slice::from_raw_parts(name_begin, name_bytecount) };
        let name = String::from_utf8_lossy(name).to_string();
        match search_dictionary(&env.dictionary, &name) {
            Some(entry) => {
                env.data_stack.push(unsafe { std::mem::transmute(entry) });
                let immediate;
                if unsafe { entry.as_ref() }.unwrap().immediate {
                    immediate = 1;
                } else {
                    immediate = -1;
                }
                env.data_stack.push(immediate);
            }
            _ => {
                env.data_stack.push(name_conuted_string);
                env.data_stack.push(0);
            }
        }
    }),
    ("2over", |env| {
        let len = env.data_stack.len();
        let x = *env.data_stack.get(len - 4).unwrap();
        let y = *env.data_stack.get(len - 3).unwrap();
        env.data_stack.push(x);
        env.data_stack.push(y);
    }),
    ("2swap", |env| {
        let x4 = env.data_stack.pop().unwrap();
        let x3 = env.data_stack.pop().unwrap();
        let x2 = env.data_stack.pop().unwrap();
        let x1 = env.data_stack.pop().unwrap();

        env.data_stack.push(x3);
        env.data_stack.push(x4);
        env.data_stack.push(x1);
        env.data_stack.push(x2);
    }),
    ("see", |env| {
        let name = env.read_name_from_input_buffer().unwrap();
        see(&env.dictionary, &name);
    }),
    ("abort", |env| {
        env.data_stack.clear();

        // TODO: Call quit instead of copying code.
        env.return_stack.clear();
        // TODO: Don't print ok
    }),
    ("environment?", |env| {
        let string_bytecount = env.data_stack.pop().unwrap() as usize;
        let string_address = env.data_stack.pop().unwrap();
        let string_address: *const u8 = unsafe { std::mem::transmute(string_address) };
        let string = unsafe { std::slice::from_raw_parts(string_address, string_bytecount) };

        let mut found = true;

        // TODO: /HOLD
        // TODO: /PAD
        // TODO: FLOORED
        // TODO: MAX-D
        // TODO: MAX-UD

        if string == "/COUNTED-STRING".as_bytes() || string == "MAX-CHAR".as_bytes() {
            env.data_stack.push(Byte::MAX as Cell);
        } else if string == "ADDRESS-UNIT-BITS".as_bytes() {
            env.data_stack.push(Cell::BITS as Cell);
        } else if string == "MAX-N".as_bytes()
            || string == "RETURN-STACK-CELLS".as_bytes()
            || string == "STACK-CELLS".as_bytes()
        {
            env.data_stack.push(Cell::MAX as Cell);
        } else if string == "MAX-U".as_bytes() {
            env.data_stack.push(usize::MAX as Cell);
        } else {
            found = false;
        }

        env.data_stack.push(match found {
            true => Flag::True,
            _ => Flag::False,
        } as Cell);
    }),
    ("evaluate", |env| {
        let string_byte_count = env.data_stack.pop().unwrap() as usize;
        let string_address = env.data_stack.pop().unwrap();
        let string_address: *const u8 = unsafe { std::mem::transmute(string_address) };
        let string = unsafe { std::slice::from_raw_parts(string_address, string_byte_count) };
        let input_buffer_head_backup = env.input_buffer_head;
        let input_buffer_backup = env.input_buffer.to_vec();

        // TODO: Set the input buffer to be `string`, don't just copy it.

        env.interpret_line(&string);

        env.input_buffer_head = input_buffer_head_backup;
        env.input_buffer.fill(0);
        for i in 0..input_buffer_backup.len() {
            *env.input_buffer.get_mut(i).unwrap() = *input_buffer_backup.get(i).unwrap();
        }
    }),
];

const IMMEDIATE_PRIMITIVES: &[(&str, Primitive)] = &[
    (";", |env| {
        env.latest().body.push(ForthOperation::Return);
        env.currently_compiling = Flag::False as Cell;
    }),
    ("if", |env| {
        env.latest().body.push(ForthOperation::BranchOnFalse(None));
    }),
    ("else", |env| {
        let unresolved_if_branch_index = env.index_of_last_unresolved_branch().unwrap();
        env.latest()
            .body
            .push(ForthOperation::PushCellToDataStack(Flag::False as Cell));
        env.latest().body.push(ForthOperation::BranchOnFalse(None));
        let branch_offset = env.latest().body.len() - unresolved_if_branch_index;
        let unresolved_branch: &mut ForthOperation = env
            .latest()
            .body
            .get_mut(unresolved_if_branch_index)
            .unwrap();
        *unresolved_branch = ForthOperation::BranchOnFalse(Some(branch_offset as isize));
    }),
    ("then", |env| {
        let unresolved_branch_index = env.index_of_last_unresolved_branch().unwrap();
        let latest = env.latest();
        let branch_offset = latest.body.len() - unresolved_branch_index;
        let unresolved_branch: &mut ForthOperation =
            latest.body.get_mut(unresolved_branch_index).unwrap();
        *unresolved_branch = ForthOperation::BranchOnFalse(Some(branch_offset as isize));
    }),
    ("begin", |env| {
        let len = env.latest().body.len();
        env.control_flow_stack.push(len);
    }),
    ("until", |env| {
        let branch_offset = env.latest().body.len() - env.control_flow_stack.pop().unwrap();
        let branch_offset = branch_offset as isize;
        let branch_offset = -branch_offset;
        env.latest()
            .body
            .push(ForthOperation::BranchOnFalse(Some(branch_offset)));
    }),
    ("while", |env| {
        env.latest().body.push(ForthOperation::BranchOnFalse(None));
    }),
    ("repeat", |env| {
        let begin_index = env.control_flow_stack.pop().unwrap();
        env.latest()
            .body
            .push(ForthOperation::PushCellToDataStack(Flag::False as Cell));
        let true_jump_offset = env.latest().body.len() - begin_index;
        let true_jump_offset = true_jump_offset as isize;
        let true_jump_offset = -true_jump_offset;
        env.latest()
            .body
            .push(ForthOperation::BranchOnFalse(Some(true_jump_offset)));

        let unresolved_while_branch_index = env.index_of_last_unresolved_branch().unwrap();
        let false_jump_offset = env.latest().body.len() - unresolved_while_branch_index;
        let false_jump_offset = false_jump_offset as isize;
        let unresolved_branch: &mut ForthOperation = env
            .latest()
            .body
            .get_mut(unresolved_while_branch_index)
            .unwrap();
        *unresolved_branch = ForthOperation::BranchOnFalse(Some(false_jump_offset));
    }),
    ("exit", |env| {
        // TODO: Don't implement as an immediate word
        //       Control the flow of execution
        env.latest().body.push(ForthOperation::Return);
    }),
    ("literal", |env| {
        let data = env.data_stack.pop().unwrap();
        let literal = ForthOperation::PushCellToDataStack(data);
        env.latest().body.push(literal);
    }),
    ("postpone", |env| {
        let name = env.read_name_from_input_buffer().unwrap();
        let entry = search_dictionary(&env.dictionary, &name).unwrap();
        let entry = unsafe { entry.as_ref() }.unwrap();
        env.latest()
            .body
            .push(ForthOperation::CallAnotherDictionaryEntry(entry));
    }),
    ("(", |env| {
        env.next_token(true, ')' as Byte);
    }),
    ("[char]", |env| {
        let (offset, length) = env.next_token(true, ' ' as Byte);
        assert_eq!(length, 1);
        let c = *env.input_buffer.get(offset).unwrap();
        env.latest()
            .body
            .push(ForthOperation::PushCellToDataStack(c as Cell));
    }),
    (".\"", |env| {
        let (offset, length) = env.next_token(false, '"' as Byte);
        let string = &env.input_buffer[offset..offset + length];

        if env.compile_mode() {
            // Write string to data space
            let data_space_string_address: *const u8 = env.data_space_pointer.as_ref().as_ptr();
            for byte in string {
                **env.data_space_pointer.nth(0).as_mut().unwrap() = *byte;
            }

            // TODO: Don't search every single time?
            let type_entry = search_dictionary(&env.dictionary, "type").unwrap();

            env.latest().body.append(&mut vec![
                ForthOperation::PushCellToDataStack(unsafe {
                    std::mem::transmute(data_space_string_address)
                }),
                ForthOperation::PushCellToDataStack(length as Cell),
                ForthOperation::CallAnotherDictionaryEntry(type_entry),
            ]);
        } else {
            print!("{}", String::from_utf8_lossy(string).to_string());
        }
    }),
    ("s\"", |env| {
        let (offset, length) = env.next_token(false, '"' as Byte);
        let string = &env.input_buffer[offset..offset + length];

        // Copy to data space
        let data_space_string_address: *const u8 = env.data_space_pointer.as_ref().as_ptr();
        for byte in string {
            **env.data_space_pointer.nth(0).as_mut().unwrap() = *byte;
        }

        if env.compile_mode() {
            env.latest().body.append(&mut vec![
                ForthOperation::PushCellToDataStack(unsafe {
                    std::mem::transmute(data_space_string_address)
                }),
                ForthOperation::PushCellToDataStack(length as Cell),
            ]);
        } else {
            env.data_stack
                .push(unsafe { std::mem::transmute(data_space_string_address) });
            env.data_stack.push(length as Cell);
        }
    }),
    ("[']", |env| {
        let name = env.read_name_from_input_buffer().unwrap();
        let entry = search_dictionary(&env.dictionary, &name).unwrap();
        env.latest()
            .body
            .push(ForthOperation::PushCellToDataStack(unsafe {
                std::mem::transmute(entry)
            }));
    }),
    ("abort\"", |env| {
        let (offset, length) = env.next_token(false, '"' as Byte);
        let abort_message_in_input_buffer = &env.input_buffer[offset..offset + length];

        // Copy to data space
        let abort_message: *const u8 = env.data_space_pointer.as_ref().as_ptr();
        let abort_message: Cell = unsafe { std::mem::transmute(abort_message) };
        for byte in abort_message_in_input_buffer {
            **env.data_space_pointer.nth(0).as_mut().unwrap() = *byte;
        }

        let abort_entry = search_dictionary(&env.dictionary, "abort").unwrap();
        let type_entry = search_dictionary(&env.dictionary, "type").unwrap();

        let mut failure_section = vec![
            ForthOperation::PushCellToDataStack(abort_message),
            ForthOperation::PushCellToDataStack(length as Cell),
            ForthOperation::CallAnotherDictionaryEntry(type_entry),
            ForthOperation::CallAnotherDictionaryEntry(abort_entry),
        ];

        let mut to_append = vec![ForthOperation::BranchOnFalse(Some(
            (failure_section.len() + 1) as isize,
        ))];

        to_append.append(&mut failure_section);

        env.latest().body.append(&mut to_append);
    }),
    ("recurse", |env| {
        let latest = env.latest();
        let call_self = ForthOperation::CallAnotherDictionaryEntry(latest);
        latest.body.push(call_self);
    }),
];

fn search_dictionary(dict: &Dictionary, name: &str) -> Option<*const DictionaryEntry> {
    let name = name.to_lowercase();
    for item in dict {
        if item.name == *name {
            return Some(item.deref());
        }
    }
    return None;
}

fn see(dict: &Dictionary, name: &str) {
    let item = search_dictionary(dict, name).unwrap();
    let item = unsafe { item.as_ref() }.unwrap();
    println!(": {} ", item.name);
    for threaded_word_entry in &item.body {
        let address = &*threaded_word_entry;
        let address: usize = unsafe { std::mem::transmute(address) };
        print!("\t${:x}:\t", address);
        match threaded_word_entry {
            ForthOperation::PushCellToDataStack(literal) => {
                print!("PUSH\t{}", literal)
            }
            ForthOperation::CallAnotherDictionaryEntry(another_entry) => {
                let another_entry = unsafe { another_entry.as_ref() }.unwrap();
                let another_entry_addr: usize = unsafe { std::mem::transmute(another_entry) };
                print!("CALL\t${:x} ({})", another_entry_addr, another_entry.name);
            }
            ForthOperation::BranchOnFalse(offset) => {
                let offset = offset.unwrap();
                let byte_offset = offset * (std::mem::size_of::<ForthOperation>() as isize);
                let dest: usize = ((address as isize) + byte_offset) as usize;
                print!("F-BR\t{} (${:x})", offset, dest);
            }
            ForthOperation::CallPrimitive(primitive) => {
                let primitive: usize = unsafe { std::mem::transmute(primitive) };
                print!("PRIM\t${:x}", primitive);
            }
            ForthOperation::Return => print!("RTN"),
        }
        println!("");
    }
    print!(";");
    if item.immediate {
        print!(" immediate");
    }
    println!("");
}

fn initial_dictionary() -> Dictionary {
    let constant_entries = CONSTANT_PRIMITIVES
        .iter()
        .map(|(name, value)| DictionaryEntry {
            name: name.to_string(),
            immediate: false,
            body: vec![
                ForthOperation::PushCellToDataStack(*value),
                ForthOperation::Return,
            ],
        });

    let execute_only_entries =
        EXECUTION_PRIMITIVES
            .iter()
            .map(|(name, exec_ptr)| DictionaryEntry {
                name: name.to_string(),
                immediate: false,
                body: vec![
                    ForthOperation::CallPrimitive(exec_ptr.clone()),
                    ForthOperation::Return,
                ],
            });

    let compile_only_entries =
        IMMEDIATE_PRIMITIVES
            .iter()
            .map(|(name, comp_ptr)| DictionaryEntry {
                name: name.to_string(),
                immediate: true,
                body: vec![
                    ForthOperation::CallPrimitive(comp_ptr.clone()),
                    ForthOperation::Return,
                ],
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
            control_flow_stack: Vec::new(),
            parsed_word: Default::default(),
        };

        for line in CORE_WORDS_INIT.lines() {
            env.interpret_line(line.as_bytes());
        }

        return env;
    }

    fn compile_mode(&self) -> bool {
        return self.currently_compiling == Flag::True as Cell;
    }

    fn latest(&mut self) -> &mut DictionaryEntry {
        return self.dictionary.front_mut().unwrap();
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

    fn interpret_line(&mut self, line: &[Byte]) {
        if line.len() == 0 {
            return;
        }

        self.input_buffer_head = 0;
        self.input_buffer.fill(0);
        for i in 0..line.len() {
            self.input_buffer[i] = *line.get(i).unwrap();
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
            _ => self.handle_text_token(token),
        }
    }

    fn handle_number_token(&mut self, token: Cell) {
        if self.compile_mode() {
            let literal = ForthOperation::PushCellToDataStack(token);
            self.latest().body.push(literal);
        } else {
            self.data_stack.push(token);
        }
    }

    fn handle_text_token(&mut self, token: &str) {
        let dict_entry = search_dictionary(&self.dictionary, token).unwrap();
        let dict_entry = unsafe { dict_entry.as_ref() }.unwrap();

        if self.compile_mode() && !dict_entry.immediate {
            self.latest()
                .body
                .push(ForthOperation::CallAnotherDictionaryEntry(dict_entry));
        } else {
            let next_word = &dict_entry.body;
            self.execute_word(next_word.first().unwrap());
        }
    }

    fn execute_word(&mut self, entry: &ForthOperation) {
        let mut instruction_pointer: *const ForthOperation = entry;
        loop {
            match unsafe { instruction_pointer.as_ref() }.unwrap() {
                ForthOperation::CallAnotherDictionaryEntry(w) => {
                    let w = unsafe { w.as_ref() }.unwrap();
                    let to_execute = &w.body;

                    let next = unsafe { instruction_pointer.add(1) };
                    self.return_stack.push(next);
                    instruction_pointer = to_execute.first().unwrap();
                    continue;
                }
                ForthOperation::PushCellToDataStack(l) => self.data_stack.push(*l),
                ForthOperation::BranchOnFalse(offset) => {
                    let cond = self.data_stack.pop().unwrap();
                    if cond == Flag::False as Cell {
                        instruction_pointer =
                            unsafe { instruction_pointer.offset(offset.unwrap()) };
                        continue;
                    }
                }
                ForthOperation::CallPrimitive(func) => func(self),
                ForthOperation::Return => match self.return_stack.pop() {
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
        for item in self.dictionary.front().unwrap().body.iter().rev() {
            index_from_the_end += 1;
            match item {
                ForthOperation::BranchOnFalse(b) => match b {
                    None => {
                        return Some(
                            self.dictionary.front().unwrap().body.len() - index_from_the_end,
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

    fn read_name_from_input_buffer(&mut self) -> Option<String> {
        let (token_offset, token_size) = self.next_token(true, ' ' as Byte);
        if token_size == 0 {
            return None;
        }

        let name =
            String::from_utf8_lossy(&self.input_buffer[token_offset..(token_offset + token_size)])
                .to_string();
        return Some(name);
    }
}

fn main() {
    let mut data_space = [0; 10 * 1024];
    let mut input_buffer = [0; 1024];
    let mut environment = Environment::new(&mut data_space, &mut input_buffer);
    loop {
        let mut line_buffer = String::new();
        std::io::stdin().read_line(&mut line_buffer).unwrap();
        line_buffer.pop();
        environment.interpret_line(&line_buffer.as_bytes());
        println!(" ok. ");
        std::io::stdout().flush().unwrap();
    }
}

#[cfg(test)]
mod tests;

use std::io::Write;
use std::ops::*;

type Cell = isize;

// TODO: Add static_assert to make sure that its bigger than Cell
type DoubleCell = i128;

const fn bool_as_cell(b: bool) -> Cell {
    match b {
        true => -1,
        _ => 0,
    }
}

type Byte = u8;

#[derive(Clone)]
enum ThreadedWordEntry {
    Literal(Cell),
    AnotherWord(*const DictionaryEntry),
    LastEntry, // Pretty much "EXIT"
}

#[derive(Clone)]
enum Word {
    Data(Cell), // TODO: Should represent variable, constant, value, etc...
    Native(fn(&mut Environment)),
    Threaded(Vec<ThreadedWordEntry>),
}

type Name = [Byte; 31];

// TODO: Compile only words
struct DictionaryEntry {
    name: Name,
    body: Word,
}

type Dictionary = std::collections::LinkedList<DictionaryEntry>;

#[derive(Clone)]
enum ReturnStackEntry {
    Word(*const Word),
    ThreadedWordEntry(*const ThreadedWordEntry),
}

struct Environment<'a> {
    data_space_pointer: std::slice::IterMut<'a, Byte>,

    data_stack: Vec<Cell>,
    return_stack: Vec<ReturnStackEntry>,

    input_buffer: &'a mut [Byte],
    input_buffer_head: usize,

    dictionary: Dictionary,

    base: Cell,

    entry_under_construction: Option<(Name, Vec<ThreadedWordEntry>)>,
}

macro_rules! binary_operator_native_word {
    ($method:tt) => {
        Word::Native(|env| {
            let b = env.data_stack.pop().unwrap();
            let a = env.data_stack.pop().unwrap();
            let c = a.$method(b);
            env.data_stack.push(c);
        })
    };
}

macro_rules! unary_operator_native_word {
    ($operator:tt) => {
	Word::Native(|env| {
            let a = env.data_stack.pop().unwrap();
	    let b = $operator a;
            env.data_stack.push(b);
	})
    }
}

macro_rules! compare_operator_native_word {
    ($operator:tt) => {
	Word::Native(|env| {
            let b = env.data_stack.pop().unwrap();
            let a = env.data_stack.pop().unwrap();
            let c = a $operator b;
            env.data_stack.push(bool_as_cell(c));
	})
    }
}
const AMOUNT_OF_CELLS_PER_ITEM: usize =
    std::mem::size_of::<ReturnStackEntry>() / std::mem::size_of::<Cell>();

const PRIMITIVES: &[(&str, Word)] = &[
    (
        ".s",
        Word::Native(|env| {
            print!("<{}> ", env.data_stack.len());
            for i in env.data_stack.iter() {
                env.print_cell(*i);
            }
        }),
    ),
    ("bye", Word::Native(|_env| std::process::exit(0))),
    (
        "words",
        Word::Native(|env| {
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
    ),
    (
        "dup",
        Word::Native(|env| {
            let x = *env.data_stack.last().unwrap();
            env.data_stack.push(x)
        }),
    ),
    (
        "drop",
        Word::Native(|env| {
            env.data_stack.pop().unwrap();
        }),
    ),
    (
        ".",
        Word::Native(|env| {
            let x = env.data_stack.pop().unwrap();
            env.print_cell(x);
        }),
    ),
    (
        "swap",
        Word::Native(|env| {
            let a = env.data_stack.pop().unwrap();
            let b = env.data_stack.pop().unwrap();
            env.data_stack.push(a);
            env.data_stack.push(b);
        }),
    ),
    (
        "over",
        Word::Native(|env| {
            let a = env.data_stack.pop().unwrap();
            let b = env.data_stack.pop().unwrap();
            env.data_stack.push(b);
            env.data_stack.push(a);
            env.data_stack.push(b);
        }),
    ),
    (
        "nip",
        Word::Native(|env| {
            let a = env.data_stack.pop().unwrap();
            env.data_stack.pop().unwrap();
            env.data_stack.push(a);
        }),
    ),
    (
        "rot",
        Word::Native(|env| {
            let a = env.data_stack.pop().unwrap();
            let b = env.data_stack.pop().unwrap();
            let c = env.data_stack.pop().unwrap();
            env.data_stack.push(b);
            env.data_stack.push(a);
            env.data_stack.push(c);
        }),
    ),
    (
        "min",
        Word::Native(|env| {
            let a = env.data_stack.pop().unwrap();
            let b = env.data_stack.pop().unwrap();
            env.data_stack.push(std::cmp::min(a, b));
        }),
    ),
    (
        "max",
        Word::Native(|env| {
            let a = env.data_stack.pop().unwrap();
            let b = env.data_stack.pop().unwrap();
            env.data_stack.push(std::cmp::max(a, b));
        }),
    ),
    (
        "abs",
        Word::Native(|env| {
            let a = env.data_stack.pop().unwrap();
            env.data_stack.push(a.abs());
        }),
    ),
    (
        "/mod",
        Word::Native(|env| {
            let n2 = env.data_stack.pop().unwrap();
            let n1 = env.data_stack.pop().unwrap();
            let n3 = n1 % n2;
            let n4 = n1 / n2;
            env.data_stack.push(n3);
            env.data_stack.push(n4);
        }),
    ),
    (
        "*/",
        Word::Native(|env| {
            let n3 = env.data_stack.pop().unwrap();
            let n2 = env.data_stack.pop().unwrap();
            let n1 = env.data_stack.pop().unwrap();

            let double_mul_result: DoubleCell = (n1 as DoubleCell) * (n2 as DoubleCell);
            let double_div_result: DoubleCell = double_mul_result / (n3 as DoubleCell);
            let result: Cell = double_div_result.try_into().unwrap();
            env.data_stack.push(result);
        }),
    ),
    (
        "*/mod",
        Word::Native(|env| {
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
    ),
    (
        "here",
        Word::Native(|env| {
            let address: *const Byte = env.data_space_pointer.as_ref().as_ptr();
            env.data_stack.push(unsafe { std::mem::transmute(address) });
        }),
    ),
    (
        "allot",
        Word::Native(|env| {
            let n = env.data_stack.pop().unwrap();
            for _ in 0..n {
                match env.data_space_pointer.next() {
                    None => panic!("Not enough memory"),
                    _ => {}
                }
            }
        }),
    ),
    (
        "@",
        Word::Native(|env| {
            let n = env.data_stack.pop().unwrap();
            let address: *mut Cell;
            let data: Cell;
            unsafe {
                address = std::mem::transmute(n);
                data = *address;
            }
            env.data_stack.push(data);
        }),
    ),
    (
        "!",
        Word::Native(|env| {
            let n = env.data_stack.pop().unwrap();
            let data = env.data_stack.pop().unwrap();
            let address: *mut Cell;
            unsafe {
                address = std::mem::transmute(n);
                *address = data;
            }
        }),
    ),
    (
        "cr",
        Word::Native(|_env| {
            println!("");
        }),
    ),
    (
        "emit",
        Word::Native(|env| {
            let n = env.data_stack.pop().unwrap();
            let c = (n as u8) as char;
            print!("{}", c);
        }),
    ),
    (
        "base",
        Word::Native(|env| {
            env.data_stack
                .push(unsafe { std::mem::transmute(&env.base) });
        }),
    ),
    ("+", binary_operator_native_word!(wrapping_add)),
    ("-", binary_operator_native_word!(wrapping_sub)),
    ("*", binary_operator_native_word!(wrapping_mul)),
    ("/", binary_operator_native_word!(div)), // TODO: Handle divide error
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
    ("bl", Word::Data(' ' as Cell)),
    ("true", Word::Data(bool_as_cell(true))),
    ("false", Word::Data(bool_as_cell(false))),
    (
        // Not a part of the core words, but its useful for debugging
        // TODO: Replace with a threaded word once compilation fully is working
        "dump",
        Word::Native(|env| {
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
        }),
    ),
    (
        ":",
        Word::Native(|env| {
            if env.entry_under_construction.is_some() {
                panic!("Can't double compile!");
            }

            let (token_offset, token_size) = env.next_token(true, ' ' as Byte);
            let mut name: Name = Default::default();
            name[0..token_size]
                .copy_from_slice(&env.input_buffer[token_offset..(token_offset + token_size)]);
            env.entry_under_construction = Some((name, Vec::new()));
        }),
    ),
    (
        ";",
        Word::Native(|env| {
            if env.entry_under_construction.is_none() {
                panic!("Using ; without : !");
            }

            let (name, mut threaded) = env.entry_under_construction.clone().unwrap();
            threaded.push(ThreadedWordEntry::LastEntry);

            // TODO: Print a message if a word is re-defined

            env.dictionary.push_front(DictionaryEntry {
                name,
                body: Word::Threaded(threaded),
            });

            env.entry_under_construction = None;
        }),
    ),
    (
        "cells",
        Word::Native(|env| {
            let n = env.data_stack.pop().unwrap();
            let result = n * (std::mem::size_of::<Cell>() as isize);
            env.data_stack.push(result);
        }),
    ),
    (
        "r>",
        Word::Native(|env| {
            let item = env.return_stack.pop().unwrap();
            let item_as_cells: &[Cell; AMOUNT_OF_CELLS_PER_ITEM] =
                unsafe { std::mem::transmute(&item) };

            for i in item_as_cells {
                env.data_stack.push(*i);
            }
        }),
    ),
    (
        ">r",
        Word::Native(|env| {
            let mut cells_to_create_return_stack_entry = [0 as Cell; AMOUNT_OF_CELLS_PER_ITEM];

            for cell in cells_to_create_return_stack_entry.iter_mut().rev() {
                cell.clone_from(&env.data_stack.pop().unwrap());
            }

            let return_stack_entry: &ReturnStackEntry =
                unsafe { std::mem::transmute(&cells_to_create_return_stack_entry) };

            env.return_stack.push(return_stack_entry.clone());
        }),
    ),
];

// TODO: Implement From?
fn name_from_str(s: &str) -> Option<Name> {
    let mut result: Name = Name::default();
    if s.len() > result.len() {
        return None;
    }

    for (i, c) in s.as_bytes().iter().enumerate() {
        result[i] = *c;
    }

    return Some(result);
}

fn search_dictionary(dict: &Dictionary, name: &str) -> Option<*const DictionaryEntry> {
    let name = name_from_str(name).unwrap();
    for item in dict {
        if item.name == name {
            return Some(item.deref());
        }
    }
    return None;
}

fn initial_dictionary() -> Dictionary {
    return std::collections::LinkedList::from_iter(PRIMITIVES.iter().map(|(a, b)| {
        DictionaryEntry {
            name: name_from_str(a).unwrap(),
            body: b.clone(),
        }
    }));
}

const CORE_WORDS_INIT: &str = ": 1+ 1 + ; \
			       : 1- 1 - ; \
			       : 0< 0 < ; \
			       : 0= 0 = ; \
			       : decimal 10 base ! ; \
			       ";

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
            entry_under_construction: None,
        };

        for line in CORE_WORDS_INIT.lines() {
            env.interpret_line(line);
        }

        return env;
    }

    fn compile_mode(&self) -> bool {
        return self.entry_under_construction.is_some();
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
                if self.input_buffer_head >= self.input_buffer.len() {
                    return (0, 0);
                }

                if *self.input_buffer.get(self.input_buffer_head).unwrap() == 0 {
                    return (0, 0);
                }

                if *self.input_buffer.get(self.input_buffer_head).unwrap() != delimiter {
                    break 'find_first_char;
                }

                self.input_buffer_head += 1;
            }
        }

        let token_begin = self.input_buffer_head;
        let token_size;

        'read_token: loop {
            if self.input_buffer_head >= self.input_buffer.len()
                || *self.input_buffer.get(self.input_buffer_head).unwrap() == 0
            {
                token_size = self.input_buffer_head - token_begin;
                break 'read_token;
            }

            if *self.input_buffer.get(self.input_buffer_head).unwrap() == delimiter {
                token_size = self.input_buffer_head - token_begin;
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
            let (_, threaded) = self.entry_under_construction.as_mut().unwrap();
            threaded.push(literal);
        } else {
            self.data_stack.push(token);
        }
    }

    fn hanle_text_token(&mut self, token: &str) {
        let dict_entry = search_dictionary(&self.dictionary, &token.to_lowercase()).unwrap();
        let dict_entry = unsafe { dict_entry.as_ref() }.unwrap();

        if self.compile_mode() && dict_entry.name[0] != ';' as Byte {
            let (_, threaded) = self.entry_under_construction.as_mut().unwrap();
            threaded.push(ThreadedWordEntry::AnotherWord(dict_entry));
        } else {
            let next_word = &dict_entry.body;
            self.execute_word(next_word);
        }
    }

    fn execute_word(&mut self, word: &Word) {
        match word {
            Word::Data(d) => self.data_stack.push(*d),
            Word::Native(f) => f(self),
            Word::Threaded(t) => self.execute_threaded_word(t.first().unwrap()),
        }
    }

    fn execute_threaded_word(&mut self, entry: &ThreadedWordEntry) {
        let mut iter: *const ThreadedWordEntry = entry;
        loop {
            match unsafe { iter.as_ref() }.unwrap() {
                ThreadedWordEntry::AnotherWord(w) => {
                    let to_execute = &unsafe { w.as_ref() }.unwrap().body;
                    match to_execute {
                        Word::Threaded(_) => {
                            let next = unsafe { iter.add(1) };
                            self.return_stack
                                .push(ReturnStackEntry::ThreadedWordEntry(next));
                            return self.execute_word(to_execute); // Jump to next word
                        }
                        _ => self.execute_word(to_execute), // Continue iteration
                    }
                }
                ThreadedWordEntry::Literal(l) => self.data_stack.push(*l),
                ThreadedWordEntry::LastEntry => {
                    return match self.return_stack.pop() {
                        Some(next) => {
                            match next {
                                ReturnStackEntry::Word(w) => {
                                    self.execute_word(unsafe { w.as_ref() }.unwrap())
                                }
                                ReturnStackEntry::ThreadedWordEntry(e) => {
                                    self.execute_threaded_word(unsafe { e.as_ref() }.unwrap())
                                }
                            };
                        }
                        _ => {}
                    }
                }
            }
            iter = unsafe { iter.add(1) };
        }
    }

    fn print_cell(&self, c: Cell) {
        match self.base {
            2 => print!("{:b} ", c),
            16 => print!("{:x} ", c),
            _ => print!("{} ", c),
        }
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

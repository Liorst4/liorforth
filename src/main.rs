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
    LastEntry,
}

#[derive(Clone)]
enum Word {
    Data(Cell), // TODO: Should represent variable, constant, value, etc...
    Native(fn(&mut Environment)),
    Threaded(Vec<ThreadedWordEntry>),
}

type Name = [Byte; 31];

struct DictionaryEntry {
    name: Name,
    body: Word,
}

type Dictionary = std::collections::LinkedList<DictionaryEntry>;

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

const PRIMITIVES: &[(&str, Word)] = &[
    (
        ".s",
        Word::Native(|env| {
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
        // TODO: Replace with a threaded word once compilation is working
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
    let mut dict =
        std::collections::LinkedList::from_iter(PRIMITIVES.iter().map(|(a, b)| DictionaryEntry {
            name: name_from_str(a).unwrap(),
            body: b.clone(),
        }));

    // To test threaded words
    dict.push_front(DictionaryEntry {
        name: name_from_str("1+").unwrap(),
        body: Word::Threaded(vec![
            ThreadedWordEntry::Literal(1),
            ThreadedWordEntry::AnotherWord(search_dictionary(&dict, "+").unwrap()),
            ThreadedWordEntry::LastEntry,
        ]),
    });

    dict.push_front(DictionaryEntry {
        name: name_from_str("2+").unwrap(),
        body: Word::Threaded(vec![
            ThreadedWordEntry::Literal(1),
            ThreadedWordEntry::AnotherWord(search_dictionary(&dict, "1+").unwrap()),
            ThreadedWordEntry::AnotherWord(search_dictionary(&dict, "+").unwrap()),
            ThreadedWordEntry::LastEntry,
        ]),
    });

    return dict;
}

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
        return Environment {
            data_space_pointer: data_space.iter_mut(),
            data_stack: Vec::new(),
            return_stack: Vec::new(),
            input_buffer,
            input_buffer_head: 0,
            dictionary: initial_dictionary(),
            base: 10,
        };
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

    fn interpret_line(&mut self, line: String) {
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

            match parse_number(self.base as u32, &token) {
                Some(number) => self.data_stack.push(number),
                _ => self.execute_from_name(&token),
            }
        }
    }

    fn execute_from_name(&mut self, word: &str) {
        let dict_entry = search_dictionary(&self.dictionary, &word.to_lowercase()).unwrap();
        let next_word = &unsafe { dict_entry.as_ref() }.unwrap().body;
        self.return_stack.push(ReturnStackEntry::Word(next_word));
        return self.execute();
    }

    fn execute(&mut self) {
        while !self.return_stack.is_empty() {
            match self.return_stack.pop().unwrap() {
                ReturnStackEntry::Word(w) => match unsafe { w.as_ref() }.unwrap() {
                    Word::Data(data) => self.data_stack.push(*data),
                    Word::Native(func) => func(self),
                    Word::Threaded(t) => self
                        .return_stack
                        .push(ReturnStackEntry::ThreadedWordEntry(t.as_ptr())),
                },
                ReturnStackEntry::ThreadedWordEntry(t) => {
                    let next_entry = unsafe { t.add(1).as_ref() }.unwrap();
                    match next_entry {
                        ThreadedWordEntry::LastEntry => {}
                        _ => self
                            .return_stack
                            .push(ReturnStackEntry::ThreadedWordEntry(next_entry)),
                    };
                    match unsafe { t.as_ref() }.unwrap() {
                        ThreadedWordEntry::Literal(l) => self.data_stack.push(*l),
                        ThreadedWordEntry::AnotherWord(w) => {
                            self.return_stack
                                .push(ReturnStackEntry::Word(&unsafe { w.as_ref() }.unwrap().body));
                        }
                        ThreadedWordEntry::LastEntry => {}
                    };
                }
            }
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
        environment.interpret_line(line_buffer);
        println!(" ok. ");
        std::io::stdout().flush().unwrap();
    }
}

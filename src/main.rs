use std::io::Write;
use std::ops::*;

type Cell = isize;

// TODO: Add static_assert to make sure that its bigger than Cell
type DoubleCell = i128;

const fn bool_as_cell(b: bool) -> Cell {
    if b {
        return -1;
    }
    return 0;
}

type Byte = u8;

#[derive(Clone, Copy)]
enum Word {
    Literal(Cell),
    Native(fn(&mut Environment)),
    // TODO: Threaded
}

struct Environment<'a> {
    // TODO: Borrowed memory span
    data_space: Vec<Byte>,

    data_space_pointer: *mut Byte,

    data_stack: Vec<Cell>,
    return_stack: Vec<&'a Word>,

    input_buffer: Vec<Byte>,

    dictionary: std::collections::HashMap<String, Word>,

    base: u32,
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

const INITIAL_DICTIONAY: &[(&str, Word)] = &[
    (
        ".s",
        Word::Native(|env| {
            for i in env.data_stack.iter() {
                print!("{} ", i);
            }
        }),
    ),
    ("bye", Word::Native(|_env| std::process::exit(0))),
    (
        "words",
        Word::Native(|env| {
            for (name, _) in env.dictionary.iter() {
                println!("{}", name);
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
            print!("{} ", x);
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
            let address_as_cell: Cell;

            unsafe {
                address_as_cell = std::mem::transmute(env.data_space_pointer);
            }

            env.data_stack.push(address_as_cell);
        }),
    ),
    (
        "allot",
        Word::Native(|env| {
            let n = env.data_stack.pop().unwrap();
            unsafe {
                env.data_space_pointer = env.data_space_pointer.add(n as usize);
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
    ("bl", Word::Literal(' ' as Cell)),
    ("true", Word::Literal(bool_as_cell(true))),
    ("false", Word::Literal(bool_as_cell(false))),
];

const DATA_SPACE_SIZE: usize = 10 * 1024;

impl<'a> Environment<'a> {
    fn new() -> Environment<'a> {
        let mut data_space = Vec::with_capacity(DATA_SPACE_SIZE);
        let data_space_pointer = data_space.as_mut_ptr();

        return Environment {
            data_space,
            data_space_pointer,
            data_stack: Vec::new(),
            return_stack: Vec::new(),
            input_buffer: Vec::new(),
            dictionary: std::collections::HashMap::from_iter(
                INITIAL_DICTIONAY.iter().map(|&(a, b)| (a.to_string(), b)),
            ),
            base: 10,
        };
    }

    fn parse_number(&self, word: &str) -> Option<Cell> {
        if word.is_empty() {
            return None;
        }

        let (base, has_base_indicator) = match word.chars().nth(0).unwrap() {
            '#' => (10, true),
            '$' => (16, true),
            '%' => (2, true),
            _ => (self.base, false),
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

    fn interpret_line(&mut self, line: String) {
        if line.len() == 0 {
            return;
        }

        self.input_buffer = line.as_bytes().to_vec();
        for word in line.split(' ') {
            // TODO: Pop word from input buffer
            match self.parse_number(word) {
                Some(number) => self.data_stack.push(number),
                _ => self.execute_from_name(word),
            }
        }
    }

    fn execute_from_name(&mut self, word: &str) {
        // TODO: Without copy?
        let word_to_execute = *self.dictionary.get(&word.to_lowercase()).unwrap();
        self.execute(&word_to_execute);
    }

    fn execute(&mut self, word: &Word) {
        match word {
            Word::Literal(l) => self.data_stack.push(*l),
            Word::Native(n) => n(self),
        }

        match self.return_stack.pop() {
            Some(next_word) => self.execute(next_word),
            _ => {}
        }
    }
}

fn main() {
    let mut environment = Environment::new();
    loop {
        let mut line_buffer = String::new();
        std::io::stdin().read_line(&mut line_buffer).unwrap();
        line_buffer.pop();
        environment.interpret_line(line_buffer);
        println!(" ok. ");
        std::io::stdout().flush().unwrap();
    }
}

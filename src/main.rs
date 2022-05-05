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
enum Word {
    Literal(Cell),
    Native(fn(&mut Environment)),
    Threaded(Vec<Word /* TODO: Use pointers to existing words when possible */>),
}

struct Environment<'a> {
    data_space_pointer: std::slice::IterMut<'a, Byte>,

    data_stack: Vec<Cell>,
    return_stack: Vec<std::collections::VecDeque<Word>>,

    dictionary: std::collections::HashMap<String, Word>,

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
    ("bl", Word::Literal(' ' as Cell)),
    ("true", Word::Literal(bool_as_cell(true))),
    ("false", Word::Literal(bool_as_cell(false))),
];

fn initial_dictionary() -> std::collections::HashMap<String, Word> {
    let mut dict = std::collections::HashMap::from_iter(
        PRIMITIVES.iter().map(|(a, b)| (a.to_string(), b.clone())),
    );

    // To test threaded words
    dict.insert(
        "1+".to_string(),
        Word::Threaded(vec![
            Word::Literal(1),
            dict.get(&"+".to_string()).unwrap().clone(),
        ]),
    );

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
    fn new(data_space: &'a mut [Byte]) -> Environment<'a> {
        return Environment {
            data_space_pointer: data_space.iter_mut(),
            data_stack: Vec::new(),
            return_stack: Vec::new(),
            dictionary: initial_dictionary(),
            base: 10,
        };
    }

    fn interpret_line(&mut self, line: String) {
        if line.len() == 0 {
            return;
        }

        for word in line.split(' ') {
            // TODO: Pop word from input buffer
            match parse_number(self.base as u32, word) {
                Some(number) => self.data_stack.push(number),
                _ => self.execute_from_name(word),
            }
        }
    }

    fn execute_from_name(&mut self, word: &str) {
        let word_to_execute = self.dictionary.get(&word.to_lowercase()).unwrap().clone();
        self.execute(word_to_execute);
    }

    fn execute(&mut self, word: Word) {
        match word {
            Word::Literal(l) => self.data_stack.push(l),
            Word::Native(n) => n(self),
            Word::Threaded(t) => {
                // TODO: Is this horribly slow?
                self.return_stack.push(t.try_into().unwrap())
            }
        }

        while !self.return_stack.is_empty() {
            if self.return_stack.last().unwrap().is_empty() {
                self.return_stack.pop();
                continue;
            }

            let next = self.return_stack.last_mut().unwrap().pop_front().unwrap();
            self.execute(next);
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
    let mut environment = Environment::new(&mut data_space);
    loop {
        let mut line_buffer = String::new();
        std::io::stdin().read_line(&mut line_buffer).unwrap();
        line_buffer.pop();
        environment.interpret_line(line_buffer);
        println!(" ok. ");
        std::io::stdout().flush().unwrap();
    }
}

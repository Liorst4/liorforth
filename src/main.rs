type Cell = isize;

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

    // TODO: Actual pointer instead of index
    data_space_pointer: usize,

    data_stack: Vec<Cell>,
    return_stack: Vec<&'a Word>,

    input_buffer: Vec<Byte>,

    dictionary: std::collections::HashMap<String, Word>,
}

macro_rules! binary_operator_native_word {
    ($operator:tt) => {
	Word::Native(|env| {
	    // TODO: Allow under/overflow
            let b = env.data_stack.pop().unwrap();
            let a = env.data_stack.pop().unwrap();
            let c = a $operator b;
            env.data_stack.push(c);
	})
    }
}

macro_rules! unary_operator_native_word {
    ($operator:tt) => {
	Word::Native(|env| {
	    // TODO: Allow under/overflow
            let a = env.data_stack.pop().unwrap();
	    let b = $operator a;
            env.data_stack.push(b);
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
            print!("{}", "\n");
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
            println!("{}", x);
        }),
    ),
    ("+", binary_operator_native_word!(+)),
    ("-", binary_operator_native_word!(-)),
    ("*", binary_operator_native_word!(*)),
    ("/", binary_operator_native_word!(/)), // TODO: Handle divide error
    ("and", binary_operator_native_word!(&)),
    ("or", binary_operator_native_word!(|)),
    ("negate", unary_operator_native_word!(-)),
    ("invert", unary_operator_native_word!(!)),
];

const DATA_SPACE_SIZE: usize = 10 * 1024;

impl<'a> Environment<'a> {
    fn new() -> Environment<'a> {
        return Environment {
            data_space: Vec::with_capacity(DATA_SPACE_SIZE),
            data_space_pointer: 0,
            data_stack: Vec::new(),
            return_stack: Vec::new(),
            input_buffer: Vec::new(),
            dictionary: std::collections::HashMap::from_iter(
                INITIAL_DICTIONAY.iter().map(|&(a, b)| (a.to_string(), b)),
            ),
        };
    }

    fn interpret_line(&mut self, line: String) {
        if line.len() == 0 {
            return;
        }

        self.input_buffer = line.as_bytes().to_vec();
        for word in line.split(' ') {
            // TODO: Pop word from input buffer

            // TODO: Hex numbers
	    // TODO: Negative numbers
            if word.chars().all(|c| c.is_numeric()) {
                self.data_stack.push(word.parse().unwrap())
            } else {
                self.execute_from_name(word);
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
    }
}

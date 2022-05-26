use std::io::Write;
use std::ops::*;

type Cell = isize;

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
    BranchOnFalse(isize /* offset */),
    LastEntry, // Pretty much "EXIT"
}

#[derive(Clone)]
enum Word {
    Primitive(Primitive),
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

    control_flow_stack: Vec<Vec<ThreadedWordEntry>>,
    name_of_entry_under_construction: Option<Name>,
}

const fn bool_as_cell(b: bool) -> Cell {
    match b {
        true => -1,
        _ => 0,
    }
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
            env.data_stack.push(bool_as_cell(c));
	}
    }
}
const AMOUNT_OF_CELLS_PER_ITEM: usize =
    std::mem::size_of::<ReturnStackEntry>() / std::mem::size_of::<Cell>();

const PRIMITIVES: &[(&str, Primitive)] = &[
    (".s", |env| {
        print!("<{}> ", env.data_stack.len());
        for i in env.data_stack.iter() {
            env.print_cell(*i);
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
        env.print_cell(x);
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
        if !env.control_flow_stack.is_empty() {
            panic!("Can't double compile!");
        }

        let (token_offset, token_size) = env.next_token(true, ' ' as Byte);
        env.name_of_entry_under_construction = Some(Default::default());
        env.name_of_entry_under_construction.as_mut().unwrap()[0..token_size]
            .copy_from_slice(&env.input_buffer[token_offset..(token_offset + token_size)]);
        env.control_flow_stack.push(Vec::new());
    }),
    (";", |env| {
        if env.control_flow_stack.is_empty() {
            panic!("Using ; without : !");
        }

        if env.control_flow_stack.len() != 1 {
            panic!("Control flow stack is not empty!");
        }

        let mut threaded = env.control_flow_stack.pop().unwrap();
        threaded.push(ThreadedWordEntry::LastEntry);
        let threaded = threaded;

        // TODO: Print a message if a word is re-defined

        env.dictionary.push_front(DictionaryEntry {
            name: env.name_of_entry_under_construction.unwrap(),
            body: Word::Threaded(threaded),
        });

        env.name_of_entry_under_construction = None;
    }),
    ("if", |env| {
        env.control_flow_stack.push(Vec::new());
    }),
    ("then", |env| {
        let mut true_section = env.control_flow_stack.pop().unwrap();
        let offset = true_section.len() + 1;
        let mut branch = vec![ThreadedWordEntry::BranchOnFalse(offset.try_into().unwrap())];
        branch.append(&mut true_section);

        if env.control_flow_stack.is_empty() {
            panic!("");
        } else {
            env.control_flow_stack
                .last_mut()
                .unwrap()
                .append(&mut branch);
        }
    }),
    ("begin", |env| {
        env.control_flow_stack.push(Vec::new());
    }),
    ("until", |env| {
        let mut branch = env.control_flow_stack.pop().unwrap();
        let offset: isize = -(branch.len() as isize);
        branch.push(ThreadedWordEntry::BranchOnFalse(offset));

        if env.control_flow_stack.is_empty() {
            panic!("");
        } else {
            env.control_flow_stack
                .last_mut()
                .unwrap()
                .append(&mut branch);
        }
    }),
    ("cells", |env| {
        let n = env.data_stack.pop().unwrap();
        let result = n * (std::mem::size_of::<Cell>() as isize);
        env.data_stack.push(result);
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
        print!("{} ", u);
    }),
    ("u<", |env| {
        let s2 = env.data_stack.pop().unwrap();
        let s1 = env.data_stack.pop().unwrap();
        let u2 = s2 as usize;
        let u1 = s1 as usize;
        let result = bool_as_cell(u1 < u2);
        env.data_stack.push(result);
    }),
    ("move", |env| {
        let length = env.data_stack.pop().unwrap() as usize;

        let dest: *mut Byte = unsafe { std::mem::transmute(env.data_stack.pop().unwrap()) };
        let src: *const Byte = unsafe { std::mem::transmute(env.data_stack.pop().unwrap()) };

        let src: &[Byte] = unsafe { std::slice::from_raw_parts(src, length) };
        let dest: &mut [Byte] = unsafe { std::slice::from_raw_parts_mut(dest, length) };

        dest.copy_from_slice(src);
    }),
    ("cell+", |env| {
        let address: *const Cell = unsafe { std::mem::transmute(env.data_stack.pop().unwrap()) };
        let address = unsafe { address.add(1) };
        let address: Cell = unsafe { std::mem::transmute(address) };
        env.data_stack.push(address);
    }),
    ("depth", |env| {
        env.data_stack.push(env.data_stack.len() as Cell);
    }),
    ("?dup", |env| {
        let number = *env.data_stack.last().unwrap();
        if number != 0 {
            env.data_stack.push(number);
        }
    }),
];

// TODO: Don't use a hard coded list
const WORDS_TO_EXECUTE_DURING_COMPILATION: [&str; 5] = [";", "if", "then", "begin", "until"];

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
    return std::collections::LinkedList::from_iter(PRIMITIVES.iter().map(|(name, ptr)| {
        DictionaryEntry {
            name: name_from_str(name).unwrap(),
            body: Word::Primitive(ptr.clone()),
        }
    }));
}

const CORE_WORDS_INIT: &str = ": 1+ 1 + ; \
			       : 1- 1 - ; \
			       : 0< 0 < ; \
			       : 0= 0 = ; \
			       : decimal 10 base ! ; \
			       : bl 32 ; \
			       : true -1 ; \
			       : false 0 ; \
			       : , here 1 cells allot ! ; \
			       : c, here 1 allot c! ; \
			       : cr 10 emit ; \
			       : space bl emit ; \
			       : / /mod swap drop ; \
			       : +! dup @ swap rot rot + swap ! ; \
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
            control_flow_stack: Vec::new(),
            name_of_entry_under_construction: None,
        };

        for line in CORE_WORDS_INIT.lines() {
            env.interpret_line(line);
        }

        return env;
    }

    fn compile_mode(&self) -> bool {
        return !self.control_flow_stack.is_empty();
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
            self.control_flow_stack.last_mut().unwrap().push(literal);
        } else {
            self.data_stack.push(token);
        }
    }

    fn hanle_text_token(&mut self, token: &str) {
        let dict_entry = search_dictionary(&self.dictionary, &token.to_lowercase()).unwrap();
        let dict_entry = unsafe { dict_entry.as_ref() }.unwrap();

        let compilation_word = WORDS_TO_EXECUTE_DURING_COMPILATION
            .iter()
            .any(|item| item == &token);

        if self.compile_mode() && !compilation_word {
            let another_word = ThreadedWordEntry::AnotherWord(dict_entry);
            self.control_flow_stack
                .last_mut()
                .unwrap()
                .push(another_word);
        } else {
            let next_word = &dict_entry.body;
            self.execute_word(next_word);
        }
    }

    fn execute_word(&mut self, word: &Word) {
        match word {
            Word::Primitive(f) => f(self),
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
                ThreadedWordEntry::BranchOnFalse(offset) => {
                    let cond = self.data_stack.pop().unwrap();
                    if cond == bool_as_cell(false) {
                        iter = unsafe { iter.offset(*offset) };
                        continue;
                    }
                }
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

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

use std::io::{Read, Write};
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

fn non_overflowing_mul(x: Cell, y: Cell) -> DoubleCell {
    return (x as DoubleCell) * (y as DoubleCell);
}

fn double_div(divided: DoubleCell, divisor: Cell) -> (Cell, Cell) {
    let divisor = divisor as DoubleCell;
    let quotient = (divided / divisor) as Cell;
    let remainder = (divided % divisor) as Cell;
    return (quotient, remainder);
}

struct Stack<'a, T>
where
    T: Copy,
{
    head: usize,
    data: &'a mut [T],
}

#[derive(Debug)]
enum StackError {
    Overflow,
    Underflow,
}

impl<'a, T> Stack<'a, T>
where
    T: Copy,
{
    fn new(data: &'a mut [T]) -> Stack<'a, T> {
        Stack { head: 0, data }
    }

    fn push(&mut self, x: T) -> Result<(), StackError> {
        if self.head + 1 >= self.data.len() {
            return Err(StackError::Overflow);
        }

        self.data[self.head] = x;
        self.head += 1;
        return Ok(());
    }

    fn pop(&mut self) -> Result<T, StackError> {
        if self.head == 0 {
            return Err(StackError::Underflow);
        }

        let result = self.data[self.head - 1];
        self.head -= 1;
        return Ok(result);
    }

    fn last(&self) -> Option<&T> {
        if self.head == 0 {
            return None;
        }

        return Some(&self.data[self.head - 1]);
    }

    fn len(&self) -> usize {
        return self.head;
    }

    fn clear(&mut self) {
        self.head = 0;
    }

    #[allow(unused)]
    fn is_empty(&self) -> bool {
        self.head == 0
    }
}

impl<'a> Stack<'a, Cell> {
    fn push_double_cell(&mut self, value: DoubleCell) -> Result<(), StackError> {
        let cells: &[Cell; 2] = unsafe { std::mem::transmute(&value) };
        self.push(cells[0])?;
        return match self.push(cells[1]) {
            Ok(_) => Ok(()),
            Err(error) => {
                self.pop().unwrap();
                Err(error)
            }
        };
    }

    fn pop_double_cell(&mut self) -> Result<DoubleCell, StackError> {
        if self.len() < 2 {
            return Err(StackError::Underflow);
        }

        let result =
            *unsafe { std::mem::transmute::<&Cell, &DoubleCell>(&self.data[self.len() - 2]) };
        self.pop().unwrap();
        self.pop().unwrap();
        return Ok(result);
    }
}

type Byte = u8;

#[repr(C)]
struct CountedString {
    len: Byte,
    data: [Byte; 0],
}

impl CountedString {
    unsafe fn as_slice<'a>(&'a self) -> &'a [Byte] {
        return core::slice::from_raw_parts(self.data.as_ptr(), self.len as usize);
    }

    unsafe fn from_slice<'a>(src: &[Byte], dst: &'a mut [Byte]) -> Option<&'a CountedString> {
        if src.len() > (Byte::MAX as usize) {
            return None;
        }

        if dst.len() < (src.len() + 1) {
            return None;
        }

        dst[0] = src.len() as Byte;
        dst[1..(1 + src.len())].copy_from_slice(src);
        return Some(std::mem::transmute(dst.as_ptr()));
    }
}

/// Native code to execute from the forth environment
type Primitive = fn(&mut Environment);

/// Used when compiling conditionals and loops
#[derive(Clone, Debug)]
enum UnresolvedOperation {
    If,
    Else,
    While,
    Leave,
}

#[derive(Clone)]
enum ForthOperation {
    PushCellToDataStack(Cell),
    CallAnotherDictionaryEntry(*const DictionaryEntry),

    // TODO: Implement as a primitive
    BranchOnFalse(isize /* offset */),
    Branch(*const ForthOperation), /* TODO: Merge with BranchOnFalse? */

    CallPrimitive(Primitive),

    // TODO: Implement as a primitive
    Return,

    /// Used when compiling conditionals and loops
    Unresolved(UnresolvedOperation),
}

impl std::fmt::Display for ForthOperation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let address = &self;
        let address: usize = unsafe { std::mem::transmute(address) };
        write!(f, "${:x}:\t", address)?;
        match self {
            ForthOperation::PushCellToDataStack(literal) => write!(f, "PUSH\t{}", literal),
            ForthOperation::CallAnotherDictionaryEntry(another_entry) => {
                let another_entry = unsafe { another_entry.as_ref() }.unwrap();
                let another_entry_addr: usize = unsafe { std::mem::transmute(another_entry) };
                write!(
                    f,
                    "CALL\t${:x} ({})",
                    another_entry_addr, another_entry.name
                )
            }
            ForthOperation::BranchOnFalse(offset) => {
                let byte_offset = offset * (std::mem::size_of::<ForthOperation>() as isize);
                let dest: usize = ((address as isize) + byte_offset) as usize;
                write!(f, "F-BR\t{} (${:x})", offset, dest)
            }
            ForthOperation::Branch(destination) => {
                let destination_address: Cell = unsafe { std::mem::transmute(*destination) };
                write!(f, "BR\t${:x}", destination_address)
            }
            ForthOperation::CallPrimitive(primitive) => {
                let primitive: usize = unsafe { std::mem::transmute(primitive) };
                write!(f, "PRIM\t${:x}", primitive)
            }
            ForthOperation::Return => write!(f, "RTN"),
            ForthOperation::Unresolved(x) => write!(f, "UNR\t{:?}", x),
        }
    }
}

const NAME_BYTE_COUNT: usize = 31;

#[derive(Default, PartialEq)]
struct Name {
    value: [Byte; NAME_BYTE_COUNT],
}

impl Name {
    fn from_ascii(s: &[Byte]) -> Name {
        let mut n = Name::default();
        n.value[0..s.len()].copy_from_slice(s);
        n.value.make_ascii_lowercase();
        return n;
    }
}

impl std::fmt::Display for Name {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut non_null_content = self.value.as_slice();
        for i in 0..self.value.len() {
            if self.value[i] == 0 {
                non_null_content = &self.value[0..i];
                break;
            }
        }
        write!(f, "{}", core::str::from_utf8(non_null_content).unwrap())
    }
}

/// A forth word
struct DictionaryEntry {
    name: Name,

    /// Execute word during compilation
    immediate: bool,

    /// Operations to perform when executing
    body: Vec<ForthOperation>,
}

impl std::fmt::Display for DictionaryEntry {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, ": {} ", self.name)?;
        for threaded_word_entry in &self.body {
            writeln!(f, "\t{}", threaded_word_entry)?
        }
        write!(f, ";")?;
        if self.immediate {
            write!(f, " immediate")?;
        }
        writeln!(f, "")
    }
}

type Dictionary = std::collections::LinkedList<DictionaryEntry>;

#[derive(Copy, Clone, Default)]
struct LoopState {
    iteration_index: Cell,
    limit: Cell,
}

struct Environment<'a> {
    data_space_pointer: std::slice::IterMut<'a, Byte>,

    data_stack: Stack<'a, Cell>,
    return_stack: Stack<'a, *const ForthOperation>,

    input_buffer: &'a mut [Byte],
    input_buffer_head: Cell,

    dictionary: Dictionary,

    base: Cell,

    currently_compiling: Cell,
    control_flow_stack: Stack<'a, usize>,

    parsed_word: &'a mut [Byte],

    runtime_loops: Stack<'a, LoopState>,
}

const USUAL_LEADING_DELIMITERS_TO_IGNORE: &[Byte] = &[' ' as Byte, '\t' as Byte];

macro_rules! binary_operator_native_word {
    ($method:tt) => {
        |env| {
            let b = env.data_stack.pop().unwrap();
            let a = env.data_stack.pop().unwrap();
            let c = a.$method(b);
            env.data_stack.push(c).unwrap();
        }
    };
}

macro_rules! unary_operator_native_word {
    ($operator:tt) => {
	|env| {
            let a = env.data_stack.pop().unwrap();
	    let b = $operator a;
            env.data_stack.push(b).unwrap();
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
            env.data_stack.push(f as Cell).unwrap();
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
        let len = env.data_stack.len();
        print!("<{}> ", len);
        for i in &env.data_stack.data[0..len] {
            env.print_number(i);
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
        env.data_stack.push(x).unwrap()
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
        env.data_stack.push(a).unwrap();
        env.data_stack.push(b).unwrap();
    }),
    ("over", |env| {
        let a = env.data_stack.pop().unwrap();
        let b = env.data_stack.pop().unwrap();
        env.data_stack.push(b).unwrap();
        env.data_stack.push(a).unwrap();
        env.data_stack.push(b).unwrap();
    }),
    ("rot", |env| {
        let a = env.data_stack.pop().unwrap();
        let b = env.data_stack.pop().unwrap();
        let c = env.data_stack.pop().unwrap();
        env.data_stack.push(b).unwrap();
        env.data_stack.push(a).unwrap();
        env.data_stack.push(c).unwrap();
    }),
    ("/mod", |env| {
        let divisor = env.data_stack.pop().unwrap();
        let divided = env.data_stack.pop().unwrap();
        let remainder = divided % divisor;
        let quotient = divided / divisor; // TODO: Handle 0?
        env.data_stack.push(remainder).unwrap();
        env.data_stack.push(quotient).unwrap();
    }),
    ("here", |env| {
        let address: *const Byte = env.data_space_pointer.as_ref().as_ptr();
        env.data_stack
            .push(unsafe { std::mem::transmute(address) })
            .unwrap();
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
            data = std::ptr::read_unaligned(address);
        }
        env.data_stack.push(data).unwrap();
    }),
    ("!", |env| {
        let n = env.data_stack.pop().unwrap();
        let data = env.data_stack.pop().unwrap();
        let address: *mut Cell;
        unsafe {
            address = std::mem::transmute(n);
            std::ptr::write_unaligned(address, data);
        }
    }),
    ("c@", |env| {
        let n = env.data_stack.pop().unwrap();
        let address: *mut Byte;
        let data: Byte;
        unsafe {
            address = std::mem::transmute(n);
            data = std::ptr::read_unaligned(address);
        }
        env.data_stack.push(data as Cell).unwrap();
    }),
    ("c!", |env| {
        let n = env.data_stack.pop().unwrap();
        let data = env.data_stack.pop().unwrap() as Byte;
        let address: *mut Byte;
        unsafe {
            address = std::mem::transmute(n);
            std::ptr::write_unaligned(address, data);
        }
    }),
    ("emit", |env| {
        let n = env.data_stack.pop().unwrap();
        let c = (n as u8) as char;
        print!("{}", c);
    }),
    ("base", |env| {
        env.data_stack
            .push(unsafe { std::mem::transmute(&env.base) })
            .unwrap();
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
            .push(unsafe { std::mem::transmute(from_return_stack) })
            .unwrap();

        env.return_stack.push(calling_word_return_address).unwrap();
    }),
    (">r", |env| {
        let calling_word_return_address = env.return_stack.pop().unwrap();

        let from_data_stack = env.data_stack.pop().unwrap();
        env.return_stack
            .push(unsafe { std::mem::transmute(from_data_stack) })
            .unwrap();

        env.return_stack.push(calling_word_return_address).unwrap();
    }),
    ("r@", |env| {
        let calling_word_return_address = env.return_stack.pop().unwrap();

        let from_return_stack = env.return_stack.last().unwrap().clone();
        env.data_stack
            .push(unsafe { std::mem::transmute(from_return_stack) })
            .unwrap();

        env.return_stack.push(calling_word_return_address).unwrap();
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
        env.data_stack.push(result as Cell).unwrap();
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
        env.data_stack.push(env.data_stack.len() as Cell).unwrap();
    }),
    ("quit", |env| {
        env.return_stack.clear();
        // TODO: Don't print ok after execution
    }),
    (">in", |env| {
        let address: Cell = unsafe { std::mem::transmute(&env.input_buffer_head) };
        env.data_stack.push(address).unwrap();
    }),
    ("state", |env| {
        let address: Cell = unsafe { std::mem::transmute(&env.currently_compiling) };
        env.data_stack.push(address).unwrap();
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
        env.data_stack.push(address).unwrap();
        env.data_stack.push(size).unwrap();
    }),
    ("immediate", |env| {
        env.latest_mut().immediate = true;
    }),
    ("align", |env| env.align_data_pointer()),
    ("word", |env| {
        let delimiter = env.data_stack.pop().unwrap();
        let token = env.next_token(USUAL_LEADING_DELIMITERS_TO_IGNORE, delimiter as Byte);
        let token = token.to_owned(); // TODO: Copy into stack instead of heap (use alloca?)
        let token = unsafe { CountedString::from_slice(&token, env.parsed_word).unwrap() };
        env.data_stack
            .push(unsafe { std::mem::transmute(token) })
            .unwrap();
    }),
    ("count", |env| {
        let counted_string_address = env.data_stack.pop().unwrap();
        let counted_string: &CountedString = unsafe {
            std::mem::transmute::<Cell, *const CountedString>(counted_string_address)
                .as_ref()
                .unwrap()
        };

        let address_of_first_character: *const Byte = counted_string.data.as_ptr();
        let byte_count = counted_string.len;

        env.data_stack
            .push(address_of_first_character as Cell)
            .unwrap();
        env.data_stack.push(byte_count as Cell).unwrap();
    }),
    ("'", |env| {
        let name = env.read_name_from_input_buffer().unwrap();
        let entry = search_dictionary(&env.dictionary, &name).unwrap();
        env.data_stack
            .push(unsafe { std::mem::transmute(entry) })
            .unwrap();
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
            ForthOperation::PushCellToDataStack(result) => env.data_stack.push(*result).unwrap(),
            _ => panic!("Invalid argument given to >body"),
        }
    }),
    ("find", |env| {
        let name_address = env.data_stack.pop().unwrap();
        let name: &CountedString = unsafe {
            std::mem::transmute::<Cell, *const CountedString>(name_address)
                .as_ref()
                .unwrap()
        };
        let name = Name::from_ascii(unsafe { name.as_slice() });
        match search_dictionary(&env.dictionary, &name) {
            Some(entry) => {
                env.data_stack
                    .push(unsafe { std::mem::transmute(entry) })
                    .unwrap();
                let immediate;
                if entry.immediate {
                    immediate = 1;
                } else {
                    immediate = -1;
                }
                env.data_stack.push(immediate).unwrap();
            }
            _ => {
                env.data_stack.push(name_address).unwrap();
                env.data_stack.push(0).unwrap();
            }
        }
    }),
    ("see", |env| {
        let name = env.read_name_from_input_buffer().unwrap();
        let item = search_dictionary(&env.dictionary, &name).unwrap();
        println!("{}", item);
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
        // TODO: MAX-UD

        if string == "/COUNTED-STRING".as_bytes() || string == "MAX-CHAR".as_bytes() {
            env.data_stack.push(Byte::MAX as Cell).unwrap();
        } else if string == "ADDRESS-UNIT-BITS".as_bytes() {
            env.data_stack.push(Cell::BITS as Cell).unwrap();
        } else if string == "MAX-N".as_bytes()
            || string == "RETURN-STACK-CELLS".as_bytes()
            || string == "STACK-CELLS".as_bytes()
        {
            env.data_stack.push(Cell::MAX as Cell).unwrap();
        } else if string == "MAX-U".as_bytes() {
            env.data_stack.push(usize::MAX as Cell).unwrap();
        } else if string == "MAX-D".as_bytes() {
            env.data_stack.push_double_cell(DoubleCell::MAX).unwrap();
        } else if string == "FLOORED".as_bytes() {
            env.data_stack.push(Flag::False as Cell).unwrap();
        } else {
            found = false;
        }

        env.data_stack
            .push(match found {
                true => Flag::True,
                _ => Flag::False,
            } as Cell)
            .unwrap();
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
    ("unloop", unloop_primitive),
    ("i", |env| {
        env.data_stack
            .push(env.runtime_loops.data.get(0).unwrap().iteration_index)
            .unwrap();
    }),
    ("j", |env| {
        env.data_stack
            .push(env.runtime_loops.data.get(1).unwrap().iteration_index)
            .unwrap();
    }),
    ("does>", |env| {
        // The address of the first operation after the "does>" itself
        let calling_word_return_address = env.return_stack.pop().unwrap();
        *env.latest_mut().body.last_mut().unwrap() =
            ForthOperation::Branch(calling_word_return_address);
    }),
    ("key", |env| {
        let mut key_buffer: [Byte; 1] = [0; 1];
        std::io::stdin().read_exact(&mut key_buffer).unwrap();
        env.data_stack
            .push(*key_buffer.get(0).unwrap() as Cell)
            .unwrap();
    }),
    ("accept", |env| {
        let max_length = env.data_stack.pop().unwrap();
        let max_length = max_length as usize;
        let destination = env.data_stack.pop().unwrap();
        let destination: *mut Byte = unsafe { std::mem::transmute(destination) };
        let buffer = unsafe { std::slice::from_raw_parts_mut(destination, max_length) };
        std::io::stdin().read(buffer).unwrap();
    }),
    ("m*", |env| {
        let x = env.data_stack.pop().unwrap();
        let y = env.data_stack.pop().unwrap();
        env.data_stack
            .push_double_cell(non_overflowing_mul(x, y))
            .unwrap();
    }),
    ("sm/rem", |env| {
        let divisor = env.data_stack.pop().unwrap();
        let divided = env.data_stack.pop_double_cell().unwrap();
        let (quotient, remainder) = double_div(divided, divisor);
        env.data_stack.push(remainder).unwrap();
        env.data_stack.push(quotient).unwrap();
    }),
];

const IMMEDIATE_PRIMITIVES: &[(&str, Primitive)] = &[
    (";", |env| {
        env.latest_mut().body.push(ForthOperation::Return);
        env.currently_compiling = Flag::False as Cell;
    }),
    ("if", |env| {
        env.latest_mut()
            .body
            .push(ForthOperation::Unresolved(UnresolvedOperation::If));
    }),
    ("else", |env| {
        let unresolved_if_branch_index = env.index_of_last_unresolved_if_or_else().unwrap();
        env.latest_mut()
            .body
            .push(ForthOperation::PushCellToDataStack(Flag::False as Cell));
        env.latest_mut()
            .body
            .push(ForthOperation::Unresolved(UnresolvedOperation::Else));
        let branch_offset = env.latest().body.len() - unresolved_if_branch_index;
        let unresolved_branch: &mut ForthOperation = env
            .latest_mut()
            .body
            .get_mut(unresolved_if_branch_index)
            .unwrap();
        *unresolved_branch = ForthOperation::BranchOnFalse(branch_offset as isize);
    }),
    ("then", |env| {
        let unresolved_branch_index = env.index_of_last_unresolved_if_or_else().unwrap();
        let latest = env.latest_mut();
        let branch_offset = latest.body.len() - unresolved_branch_index;
        let unresolved_branch: &mut ForthOperation =
            latest.body.get_mut(unresolved_branch_index).unwrap();
        *unresolved_branch = ForthOperation::BranchOnFalse(branch_offset as isize);
    }),
    ("begin", |env| {
        let len = env.latest_mut().body.len();
        env.control_flow_stack.push(len).unwrap();
    }),
    ("until", |env| {
        let branch_offset = env.latest_mut().body.len() - env.control_flow_stack.pop().unwrap();
        let branch_offset = branch_offset as isize;
        let branch_offset = -branch_offset;
        env.latest_mut()
            .body
            .push(ForthOperation::BranchOnFalse(branch_offset));
    }),
    ("while", |env| {
        env.latest_mut()
            .body
            .push(ForthOperation::Unresolved(UnresolvedOperation::While));
    }),
    ("repeat", |env| {
        let begin_index = env.control_flow_stack.pop().unwrap();
        env.latest_mut()
            .body
            .push(ForthOperation::PushCellToDataStack(Flag::False as Cell));
        let true_jump_offset = env.latest_mut().body.len() - begin_index;
        let true_jump_offset = true_jump_offset as isize;
        let true_jump_offset = -true_jump_offset;
        env.latest_mut()
            .body
            .push(ForthOperation::BranchOnFalse(true_jump_offset));

        let unresolved_while_branch_index = env.index_of_last_unresolved_while().unwrap();
        let false_jump_offset = env.latest_mut().body.len() - unresolved_while_branch_index;
        let false_jump_offset = false_jump_offset as isize;
        let unresolved_branch: &mut ForthOperation = env
            .latest_mut()
            .body
            .get_mut(unresolved_while_branch_index)
            .unwrap();
        *unresolved_branch = ForthOperation::BranchOnFalse(false_jump_offset);
    }),
    ("exit", |env| {
        // TODO: Don't implement as an immediate word
        //       Control the flow of execution
        env.latest_mut().body.push(ForthOperation::Return);
    }),
    ("literal", |env| {
        let data = env.data_stack.pop().unwrap();
        let literal = ForthOperation::PushCellToDataStack(data);
        env.latest_mut().body.push(literal);
    }),
    ("postpone", |env| {
        let name = env.read_name_from_input_buffer().unwrap();
        let entry = search_dictionary(&env.dictionary, &name).unwrap();
        let operation = ForthOperation::CallAnotherDictionaryEntry(entry);
        env.latest_mut().body.push(operation);
    }),
    ("(", |env| {
        env.next_token(&[], ')' as Byte);
    }),
    ("s\"", |env| {
        let string = env.next_token(&[], '"' as Byte).to_owned(); // TODO: Possible without copying to heap?
        let length = string.len();

        // Copy to data space
        let data_space_string_address: *const u8 = env.data_space_pointer.as_ref().as_ptr();
        for byte in string {
            **env.data_space_pointer.nth(0).as_mut().unwrap() = byte;
        }

        if env.compile_mode() {
            env.latest_mut().body.append(&mut vec![
                ForthOperation::PushCellToDataStack(unsafe {
                    std::mem::transmute(data_space_string_address)
                }),
                ForthOperation::PushCellToDataStack(length as Cell),
            ]);
        } else {
            env.data_stack
                .push(unsafe { std::mem::transmute(data_space_string_address) })
                .unwrap();
            env.data_stack.push(length as Cell).unwrap();
        }
    }),
    ("recurse", |env| {
        let latest = env.latest_mut();
        let call_self = ForthOperation::CallAnotherDictionaryEntry(latest);
        latest.body.push(call_self);
    }),
    ("do", do_primitive),
    ("leave", |env| {
        env.latest_mut().body.append(&mut vec![
            ForthOperation::CallPrimitive(unloop_primitive),
            ForthOperation::PushCellToDataStack(Flag::False as Cell),
            ForthOperation::Unresolved(UnresolvedOperation::Leave),
        ]);
    }),
    ("+loop", loop_plus_primitive),
];

fn unloop_primitive(env: &mut Environment) {
    env.runtime_loops.pop().unwrap();
}

fn do_primitive(env: &mut Environment) {
    if env.compile_mode() {
        env.latest_mut()
            .body
            .push(ForthOperation::CallPrimitive(do_primitive));

        let len = env.latest_mut().body.len();
        env.control_flow_stack.push(len).unwrap();
    } else {
        let initial_index = env.data_stack.pop().unwrap();
        let limit = env.data_stack.pop().unwrap();
        env.runtime_loops
            .push(LoopState {
                iteration_index: initial_index,
                limit,
            })
            .unwrap();
    }
}

fn loop_plus_primitive(env: &mut Environment) {
    if env.compile_mode() {
        let do_index = env.control_flow_stack.pop().unwrap();

        env.latest_mut()
            .body
            .push(ForthOperation::CallPrimitive(loop_plus_primitive));

        let do_offset = env.latest_mut().body.len() - do_index;
        let do_offset = do_offset as isize;
        let do_offset = -do_offset;
        env.latest_mut()
            .body
            .push(ForthOperation::BranchOnFalse(do_offset));

        let len = env.latest().body.len();
        for index in do_index..env.latest().body.len() {
            let item = env.latest_mut().body.get_mut(index).unwrap();
            match item {
                ForthOperation::Unresolved(UnresolvedOperation::Leave) => {
                    let branch_offset = len - index;
                    let branch_offset = branch_offset as isize;
                    *item = ForthOperation::BranchOnFalse(branch_offset);
                }
                _ => {}
            }
        }
    } else {
        let mut loop_state = env.runtime_loops.pop().unwrap();
        let addition = env.data_stack.pop().unwrap();
        loop_state.iteration_index += addition;
        if loop_state.iteration_index >= loop_state.limit {
            env.data_stack.push(Flag::True as Cell).unwrap();
        } else {
            env.runtime_loops.push(loop_state).unwrap();
            env.data_stack.push(Flag::False as Cell).unwrap();
        }
    }
}

fn search_dictionary<'a>(dict: &'a Dictionary, name: &Name) -> Option<&'a DictionaryEntry> {
    for item in dict {
        if item.name == *name {
            return Some(item);
        }
    }
    return None;
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
    fn new(
        data_space: &'a mut [Byte],
        input_buffer: &'a mut [Byte],
        parsed_word_buffer: &'a mut [Byte],
        data_stack_buffer: &'a mut [Cell],
        return_stack_buffer: &'a mut [*const ForthOperation],
        control_flow_stack_buffer: &'a mut [usize],
        runtime_loops_buffer: &'a mut [LoopState],
    ) -> Environment<'a> {
        Environment {
            data_space_pointer: data_space.iter_mut(),
            data_stack: Stack::new(data_stack_buffer),
            return_stack: Stack::new(return_stack_buffer),
            input_buffer,
            input_buffer_head: 0,
            dictionary: Default::default(),
            base: 10,
            currently_compiling: Flag::False as Cell,
            control_flow_stack: Stack::new(control_flow_stack_buffer),
            parsed_word: parsed_word_buffer,
            runtime_loops: Stack::new(runtime_loops_buffer),
        }
    }

    fn load_runtime(&mut self) {
        let constant_entries = CONSTANT_PRIMITIVES
            .iter()
            .map(|(name, value)| DictionaryEntry {
                name: Name::from_ascii(name.as_bytes()),
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
                    name: Name::from_ascii(name.as_bytes()),
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
                    name: Name::from_ascii(name.as_bytes()),
                    immediate: true,
                    body: vec![
                        ForthOperation::CallPrimitive(comp_ptr.clone()),
                        ForthOperation::Return,
                    ],
                });

        let entries = constant_entries
            .chain(execute_only_entries)
            .chain(compile_only_entries);

        self.dictionary = std::collections::LinkedList::from_iter(entries);

        const FORTH_RUNTIME_INIT: &str = include_str!(concat!(env!("OUT_DIR"), "/runtime.fth"));
        for line in FORTH_RUNTIME_INIT.lines() {
            self.interpret_line(line.as_bytes());
        }
    }

    fn compile_mode(&self) -> bool {
        return self.currently_compiling == Flag::True as Cell;
    }

    fn latest(&self) -> &DictionaryEntry {
        return self.dictionary.front().unwrap();
    }

    fn latest_mut(&mut self) -> &mut DictionaryEntry {
        return self.dictionary.front_mut().unwrap();
    }

    fn next_token(&mut self, leading_delimiters: &[Byte], delimiter: Byte) -> &[Byte] {
        if !leading_delimiters.is_empty() {
            'find_first_char: loop {
                if self.input_buffer_head as usize >= self.input_buffer.len()
                    || *self
                        .input_buffer
                        .get(self.input_buffer_head as usize)
                        .unwrap()
                        == 0
                {
                    return &self.input_buffer[0..0];
                }

                if !leading_delimiters.contains(
                    self.input_buffer
                        .get(self.input_buffer_head as usize)
                        .unwrap(),
                ) {
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

        return &self.input_buffer[token_begin..token_begin + token_size];
    }

    fn interpret_line(&mut self, line: &[Byte]) {
        if line.len() == 0 {
            return;
        }

        // Reset input buffer
        self.input_buffer_head = 0;
        self.input_buffer[0..line.len()].copy_from_slice(line);
        self.input_buffer[line.len()..].fill(0);

        'empty_input_buffer: loop {
            let token = self.next_token(USUAL_LEADING_DELIMITERS_TO_IGNORE, ' ' as Byte);

            if token.len() == 0 {
                break 'empty_input_buffer;
            }

            let token: String = String::from_utf8_lossy(token).to_string();

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
            self.latest_mut().body.push(literal);
        } else {
            self.data_stack.push(token).unwrap();
        }
    }

    fn handle_text_token(&mut self, token: &str) {
        let dict_entry =
            search_dictionary(&self.dictionary, &Name::from_ascii(token.as_bytes())).unwrap();

        if self.compile_mode() && !dict_entry.immediate {
            let operation = ForthOperation::CallAnotherDictionaryEntry(dict_entry);
            self.latest_mut().body.push(operation);
        } else {
            let next_word = &dict_entry.body;
            self.execute_word(next_word.first().unwrap());
        }
    }

    fn execute_word(&mut self, entry: *const ForthOperation) {
        let mut instruction_pointer = entry;
        loop {
            match unsafe { instruction_pointer.as_ref() }.unwrap() {
                ForthOperation::CallAnotherDictionaryEntry(w) => {
                    let w = unsafe { w.as_ref() }.unwrap();
                    let to_execute = &w.body;

                    let next = unsafe { instruction_pointer.add(1) };
                    self.return_stack.push(next).unwrap();
                    instruction_pointer = to_execute.first().unwrap();
                    continue;
                }
                ForthOperation::PushCellToDataStack(l) => self.data_stack.push(*l).unwrap(),
                ForthOperation::BranchOnFalse(offset) => {
                    let cond = self.data_stack.pop().unwrap();
                    if cond == Flag::False as Cell {
                        instruction_pointer = unsafe { instruction_pointer.offset(*offset) };
                        continue;
                    }
                }
                ForthOperation::Branch(destination) => {
                    instruction_pointer = *destination;
                    continue;
                }
                ForthOperation::CallPrimitive(func) => func(self),
                ForthOperation::Return => match self.return_stack.len() {
                    0 => {
                        break; // Nothing left to execute
                    }
                    _ => {
                        instruction_pointer = self.return_stack.pop().unwrap();
                        continue;
                    }
                },
                ForthOperation::Unresolved(_) => {
                    panic!("Unresolved branch!")
                }
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

    fn reverse_find_in_latest(&self, test: fn(&ForthOperation) -> bool) -> Option<usize> {
        let mut index_from_the_end = 0;
        for item in self.latest().body.iter().rev() {
            index_from_the_end += 1;
            if test(&item) {
                return Some(self.dictionary.front().unwrap().body.len() - index_from_the_end);
            }
        }
        return None;
    }

    fn index_of_last_unresolved_if_or_else(&self) -> Option<usize> {
        return self.reverse_find_in_latest(|item| match item {
            ForthOperation::Unresolved(UnresolvedOperation::If | UnresolvedOperation::Else) => true,
            _ => false,
        });
    }

    fn index_of_last_unresolved_while(&self) -> Option<usize> {
        return self.reverse_find_in_latest(|item| match item {
            ForthOperation::Unresolved(UnresolvedOperation::While) => true,
            _ => false,
        });
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
        let name = self.next_token(USUAL_LEADING_DELIMITERS_TO_IGNORE, ' ' as Byte);
        if name.len() == 0 {
            return None;
        }

        return Some(Name::from_ascii(name));
    }
}

/// Create a forth environment with stack buffers
macro_rules! fixed_sized_buffers_environment {
    ($name:ident,
     $data_space_size:expr,
     $input_buffer_size:expr,
     $parsed_word_buffer_size:expr,
     $data_stack_size:expr,
     $return_stack_size:expr,
     $control_flow_stack_size:expr,
     $runtime_loops_stack_size:expr) => {
        // TODO: Unique identifiers for these buffers
        let mut data_space = [0; $data_space_size];
        let mut input_buffer = [0; $input_buffer_size];
        let mut parsed_word_buffer = [0; $parsed_word_buffer_size];
        let mut data_stack_buffer = [Default::default(); $data_stack_size];
        let mut return_stack_buffer = [std::ptr::null(); $return_stack_size];
        let mut control_flow_stack_buffer = [Default::default(); $control_flow_stack_size];
        let mut runtime_loops_stack_buffer = [Default::default(); $runtime_loops_stack_size];

        let mut $name = Environment::new(
            &mut data_space,
            &mut input_buffer,
            &mut parsed_word_buffer,
            &mut data_stack_buffer,
            &mut return_stack_buffer,
            &mut control_flow_stack_buffer,
            &mut runtime_loops_stack_buffer,
        );
    };
}

/// Create a static environment
macro_rules! default_fixed_sized_environment {
    ($name:ident) => {
        fixed_sized_buffers_environment!($name, 10 * 1024, 1024, 100, 100, 100, 100, 100)
    };
}

fn main() {
    default_fixed_sized_environment!(environment);
    environment.load_runtime();
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

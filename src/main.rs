// Copyright (C) 2024 Lior Stern.
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
use std::ops::{BitAnd, BitOr, BitXor, Shl, Shr};

/// Forth's basic data type. Holds a number
type Cell = isize;

/// Unsigned version of `Cell`
type UCell = usize;

/// Forth's boolean type
enum Flag {
    False = (0 as Cell),
    True = !(Flag::False as Cell),
}

impl From<bool> for Flag {
    fn from(b: bool) -> Self {
        match b {
            true => Flag::True,
            false => Flag::False,
        }
    }
}

#[cfg(target_pointer_width = "64")]
/// `Cell` with double the bits
type DoubleCell = i128;

#[cfg(target_pointer_width = "32")]
/// `Cell` with double the bits
type DoubleCell = i64;

#[cfg(target_pointer_width = "16")]
/// `Cell` with double the bits
type DoubleCell = i32;

#[cfg(target_pointer_width = "8")]
/// `Cell` with double the bits
type DoubleCell = i16;

#[cfg(target_pointer_width = "64")]
/// `UCell` with double the bits
type DoubleUCell = u128;

#[cfg(target_pointer_width = "32")]
/// `UCell` with double the bits
type DoubleUCell = u64;

#[cfg(target_pointer_width = "16")]
/// `UCell` with double the bits
type DoubleUCell = u32;

#[cfg(target_pointer_width = "8")]
/// `UCell` with double the bits
type DoubleUCell = u16;

const fn double_ucell_to_array(x: DoubleUCell) -> [UCell; 2] {
    let low = x as UCell;
    let high = (x >> UCell::BITS) as UCell;

    [low, high]
}

const fn double_ucell_from_array(x: [UCell; 2]) -> DoubleUCell {
    let low = x[0];
    let high = x[1];

    ((high as DoubleUCell) << UCell::BITS) | (low as DoubleUCell)
}

const fn double_cell_to_array(x: DoubleCell) -> [Cell; 2] {
    let ucells = double_ucell_to_array(x as DoubleUCell);

    [ucells[0] as Cell, ucells[1] as Cell]
}

const fn double_cell_from_array(x: [Cell; 2]) -> DoubleCell {
    double_ucell_from_array([x[0] as UCell, x[1] as UCell]) as DoubleCell
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

        Ok(())
    }

    fn pop(&mut self) -> Result<T, StackError> {
        if self.head == 0 {
            return Err(StackError::Underflow);
        }

        let result = self.data[self.head - 1];
        self.head -= 1;

        Ok(result)
    }

    fn last(&self) -> Option<&T> {
        if self.head == 0 {
            return None;
        }

        Some(&self.data[self.head - 1])
    }

    fn len(&self) -> usize {
        self.head
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
        let cells: [Cell; 2] = double_cell_to_array(value);
        self.push(cells[0])?;

        match self.push(cells[1]) {
            Ok(_) => Ok(()),
            Err(error) => {
                self.pop().unwrap();
                Err(error)
            }
        }
    }

    fn pop_double_cell(&mut self) -> Result<DoubleCell, StackError> {
        if self.len() < 2 {
            return Err(StackError::Underflow);
        }

        let mut result: [Cell; 2] = Default::default();
        result[1] = self.pop().unwrap();
        result[0] = self.pop().unwrap();
        let result = double_cell_from_array(result);

        Ok(result)
    }
}

type Byte = u8;

#[repr(packed(1))]
struct CountedString {
    len: Byte,
    data: [Byte; 0],
}

impl CountedString {
    unsafe fn as_slice(&self) -> &[Byte] {
        core::slice::from_raw_parts(self.data.as_ptr(), self.len as usize)
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

        Some(&*(dst.as_ptr() as *const CountedString))
    }
}

/// Native code to execute from the forth environment
type Primitive = fn(&mut Environment);

/// Used when compiling conditionals and loops
#[derive(Clone, Debug, PartialEq)]
enum UnresolvedOperation {
    If,
    Else,
    While,
    Leave,
}

impl TryFrom<Cell> for UnresolvedOperation {
    type Error = ();
    fn try_from(x: Cell) -> Result<Self, Self::Error> {
        match x {
            0 => Ok(UnresolvedOperation::If),
            1 => Ok(UnresolvedOperation::Else),
            2 => Ok(UnresolvedOperation::While),
            3 => Ok(UnresolvedOperation::Leave),
            _ => Err(()),
        }
    }
}

/// Instructions for the interpreter
#[derive(Clone, PartialEq)]
enum ForthOperation {
    /// Push the given Cell to the data stack
    PushData(Cell),

    /// Push the next operation in the current word body into the return stack.
    /// Jump to the first instruction of the given dictionary entry.
    CallEntry(*const DictionaryEntry),

    /// Pop the data stack. Jump to the given offset if the popped value is `Flag::False`
    BranchOnFalse(isize),

    /// Jump to the given operation
    Branch(*const ForthOperation),

    /// Execute the given primitive function
    CallPrimitive(Primitive),

    /// Pop the return stack, jump to the popped operation.
    Return,

    /// Used when compiling conditionals and loops
    Unresolved(UnresolvedOperation),
}

impl TryFrom<DoubleCell> for ForthOperation {
    type Error = ();
    fn try_from(x: DoubleCell) -> Result<Self, Self::Error> {
        let x = double_cell_to_array(x);
        let first = x[0];
        let second = x[1];
        match first {
            0 => Ok(ForthOperation::PushData(second)),
            1 => Ok(ForthOperation::CallEntry(second as *const DictionaryEntry)),
            2 => Ok(ForthOperation::BranchOnFalse(second)),
            3 => Ok(ForthOperation::Branch(second as *const ForthOperation)),
            4 => Ok(ForthOperation::CallPrimitive(unsafe {
                std::mem::transmute(second)
            })),
            5 => Ok(ForthOperation::Return),
            6 => Ok(ForthOperation::Unresolved(UnresolvedOperation::try_from(
                second,
            )?)),
            _ => Err(()),
        }
    }
}

impl std::fmt::Display for ForthOperation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let address = self as *const ForthOperation as usize;
        write!(f, "${:x}:\t", address)?;
        match self {
            ForthOperation::PushData(literal) => write!(f, "PUSH\t{}", literal),
            ForthOperation::CallEntry(another_entry) => {
                let another_entry_addr = *another_entry as usize;
                let name = &unsafe { another_entry.as_ref() }.unwrap().name;
                write!(
                    f,
                    "CALL\t${:x} ({})",
                    another_entry_addr,
                    name.as_str().unwrap()
                )
            }
            ForthOperation::BranchOnFalse(offset) => {
                let byte_offset = offset * (std::mem::size_of::<ForthOperation>() as isize);
                let dest: usize = ((address as isize) + byte_offset) as usize;
                write!(f, "F-BR\t{} (${:x})", offset, dest)
            }
            ForthOperation::Branch(destination) => {
                let destination_address = *destination as Cell;
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

        n
    }
}

impl<'a> Name {
    fn as_str(&'a self) -> Result<&'a str, core::str::Utf8Error> {
        let count = self.value.iter().take_while(|c| **c != 0).count();
        let non_null_content = &self.value[0..count];
        core::str::from_utf8(non_null_content)
    }
}

struct DataSpaceManager<'a> {
    unused_area: &'a mut [Byte],
}

impl<'a> DataSpaceManager<'a> {
    fn new(data_space: &'a mut [Byte]) -> Self {
        Self {
            unused_area: data_space,
        }
    }

    unsafe fn here(&mut self) -> *mut Byte {
        self.unused_area.as_mut_ptr()
    }

    fn allot(&mut self, amount: usize) -> Option<&'a mut [Byte]> {
        if self.unused_area.len() < amount {
            return None;
        }

        let area =
            unsafe { core::slice::from_raw_parts_mut(self.unused_area.as_mut_ptr(), amount) };

        let new_unused_area = unsafe {
            core::slice::from_raw_parts_mut(
                self.unused_area.as_mut_ptr().add(amount),
                self.unused_area.len() - amount,
            )
        };

        self.unused_area = new_unused_area;
        Some(area)
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
        writeln!(f, ": {} ", self.name.as_str().unwrap())?;
        for threaded_word_entry in &self.body {
            writeln!(f, "\t{}", threaded_word_entry)?
        }
        write!(f, ";")?;
        if self.immediate {
            write!(f, " immediate")?;
        }
        writeln!(f)
    }
}

type Dictionary = std::collections::LinkedList<DictionaryEntry>;

#[derive(Copy, Clone, Default)]
struct CountedLoopState {
    loop_counter: Cell,
    limit: Cell,
}

impl From<DoubleCell> for CountedLoopState {
    fn from(x: DoubleCell) -> CountedLoopState {
        let x = double_cell_to_array(x);

        CountedLoopState {
            loop_counter: x[0],
            limit: x[1],
        }
    }
}

impl From<CountedLoopState> for DoubleCell {
    fn from(val: CountedLoopState) -> DoubleCell {
        double_cell_from_array([val.loop_counter, val.limit])
    }
}

struct Environment<'a> {
    data_space_manager: DataSpaceManager<'a>,

    data_stack: Stack<'a, Cell>,
    return_stack: Stack<'a, *const ForthOperation>,

    input_buffer: &'a mut [Byte],
    input_buffer_head: Cell,

    dictionary: Dictionary,

    base: Cell,

    currently_compiling: Cell,
    control_flow_stack: Stack<'a, UCell>,

    parsed_word: &'a mut [Byte],

    counted_loop_stack: Stack<'a, CountedLoopState>,
}

const USUAL_LEADING_DELIMITERS_TO_IGNORE: &[Byte] = &[b' ', b'\t'];

struct StaticDictionaryEntry {
    name: &'static str,
    immediate: bool,
    body: ForthOperation,
}

macro_rules! declare_constant {
    ($name:literal, $value:expr) => {
        StaticDictionaryEntry {
            name: $name,
            immediate: false,
            body: ForthOperation::PushData($value as Cell),
        }
    };
}

macro_rules! declare_primitive {
    ($name:literal, $immediate:literal,  $arg:ident, $body:block) => {
        StaticDictionaryEntry {
            name: $name,
            immediate: $immediate,
            body: ForthOperation::CallPrimitive({
                #[export_name = concat!("liorforth_primitive_", $name)]
                fn primitive($arg: &mut Environment) {
                    $body
                }
                primitive
            }),
        }
    };

    ($name:literal, $arg:ident, $body:block) => {
        declare_primitive!($name, false, $arg, $body)
    };
}

macro_rules! declare_binary_operator_primitive {
    ($name:literal, $method:tt) => {
        declare_primitive!($name, env, {
            let b = env.data_stack.pop().unwrap();
            let a = env.data_stack.pop().unwrap();
            let c = a.$method(b);
            env.data_stack.push(c).unwrap();
        })
    };
}

macro_rules! declare_unary_operator_primitive {
    ($name:literal, $operator:tt) => {
	declare_primitive!($name, env, {
            let a = env.data_stack.pop().unwrap();
	    let b = $operator a;
            env.data_stack.push(b).unwrap();
	})
    };
}

macro_rules! declare_compare_operator_primitive {
    ($name:literal, $operator:tt) => {
	declare_primitive!($name, env, {
            let b = env.data_stack.pop().unwrap();
            let a = env.data_stack.pop().unwrap();
            let c = a $operator b;
	    let f : Flag = c.into();
            env.data_stack.push(f as Cell).unwrap();
	})
    };
}

macro_rules! declare_immediate_primitive {
    ($name:literal, $arg:ident, $body:block) => {
        declare_primitive!($name, true, $arg, $body)
    };
}

macro_rules! get_primitive {
    ($name:literal) => {
        {
            const fn const_compare_bytes(
		a: &'static [Byte],
		b: &'static [Byte]
	    ) -> bool {
                if a.len() != b.len() {
                    return false;
                }

                if a.is_empty() {
                    return true;
                }

		if let (
		    Some((a_first, a_rest)),
		    Some((b_first, b_rest))
		) = (a.split_first(), b.split_first()) {
                    if *a_first != *b_first {
                        return false;
                    }

                    return const_compare_bytes(a_rest, b_rest);
		}

                false
            }

            const fn get_primitive_inner(
		name: &'static str,
		dictionary: &'static [StaticDictionaryEntry]
	    ) -> Primitive {
                if let Some((first, rest)) = dictionary.split_first() {
                    if const_compare_bytes(
			first.name.as_bytes(),
			name.as_bytes()
		    ) {
                        return match first.body  {
                            ForthOperation::CallPrimitive(p) => p,
                            _ => panic!("Given static dictionary item name isn't associated with a primitive"),
                        };
                    }

                    return get_primitive_inner(name, rest);
                }
                panic!("Given name not found in static dictionary");
            }

            const ENTRY: Primitive = get_primitive_inner($name, STATIC_DICTIONARY);
	    ENTRY
        }
    };
}

const STATIC_DICTIONARY: &[StaticDictionaryEntry] = &[
    declare_constant!("true", Flag::True),
    declare_constant!("false", Flag::False),
    declare_constant!("bl", b' '),
    declare_constant!("nl", b'\n'),
    declare_constant!("sizeof-cell", std::mem::size_of::<Cell>()),
    declare_constant!("sizeof-char", std::mem::size_of::<Byte>()),
    declare_primitive!(".s", env, {
        let len = env.data_stack.len();
        print!("<{}> ", len);
        for i in &env.data_stack.data[0..len] {
            env.print_number(i);
        }
    }),
    declare_primitive!("bye", _env, { std::process::exit(0) }),
    declare_primitive!("words", env, {
        for entry in env.dictionary.iter() {
            println!("{}", entry.name.as_str().unwrap());
        }
    }),
    declare_primitive!("dup", env, {
        let x = *env.data_stack.last().unwrap();
        env.data_stack.push(x).unwrap()
    }),
    declare_primitive!("drop", env, {
        env.data_stack.pop().unwrap();
    }),
    declare_primitive!(".", env, {
        let x = env.data_stack.pop().unwrap();
        env.print_number(x);
    }),
    declare_primitive!("swap", env, {
        let a = env.data_stack.pop().unwrap();
        let b = env.data_stack.pop().unwrap();
        env.data_stack.push(a).unwrap();
        env.data_stack.push(b).unwrap();
    }),
    declare_primitive!("over", env, {
        let a = env.data_stack.pop().unwrap();
        let b = env.data_stack.pop().unwrap();
        env.data_stack.push(b).unwrap();
        env.data_stack.push(a).unwrap();
        env.data_stack.push(b).unwrap();
    }),
    declare_primitive!("rot", env, {
        let a = env.data_stack.pop().unwrap();
        let b = env.data_stack.pop().unwrap();
        let c = env.data_stack.pop().unwrap();
        env.data_stack.push(b).unwrap();
        env.data_stack.push(a).unwrap();
        env.data_stack.push(c).unwrap();
    }),
    declare_primitive!("/mod", env, {
        let divisor = env.data_stack.pop().unwrap();
        let divided = env.data_stack.pop().unwrap();
        let remainder = divided % divisor;
        let quotient = divided / divisor; // TODO: Handle 0?
        env.data_stack.push(remainder).unwrap();
        env.data_stack.push(quotient).unwrap();
    }),
    declare_primitive!("here", env, {
        let address: *mut Byte = unsafe { env.data_space_manager.here() };
        env.data_stack.push(address as Cell).unwrap();
    }),
    declare_primitive!("allot", env, {
        let n = env.data_stack.pop().unwrap();
        if n > 0 {
            env.data_space_manager
                .allot(n as usize)
                .expect("Not enough memory");
        }
    }),
    declare_primitive!("@", env, {
        let n = env.data_stack.pop().unwrap();
        let address = n as *mut Cell;
        let data = unsafe { std::ptr::read_unaligned::<Cell>(address) };
        env.data_stack.push(data).unwrap();
    }),
    declare_primitive!("!", env, {
        let n = env.data_stack.pop().unwrap();
        let data = env.data_stack.pop().unwrap();
        let address = n as *mut Cell;
        unsafe { std::ptr::write_unaligned(address, data) };
    }),
    declare_primitive!("c@", env, {
        let n = env.data_stack.pop().unwrap();
        let address = n as *mut Byte;
        let data = unsafe { std::ptr::read_unaligned::<Byte>(address) };
        env.data_stack.push(data as Cell).unwrap();
    }),
    declare_primitive!("c!", env, {
        let n = env.data_stack.pop().unwrap();
        let data = env.data_stack.pop().unwrap() as Byte;
        let address = n as *mut Byte;
        unsafe { std::ptr::write_unaligned(address, data) };
    }),
    declare_primitive!("emit", env, {
        let n = env.data_stack.pop().unwrap();
        let c = (n as u8) as char;
        print!("{}", c);
    }),
    declare_primitive!("base", env, {
        let base_address: *mut Cell = &mut env.base;
        env.data_stack.push(base_address as Cell).unwrap();
    }),
    declare_binary_operator_primitive!("+", wrapping_add),
    declare_binary_operator_primitive!("-", wrapping_sub),
    declare_binary_operator_primitive!("*", wrapping_mul),
    declare_binary_operator_primitive!("and", bitand),
    declare_binary_operator_primitive!("or", bitor),
    declare_binary_operator_primitive!("xor", bitxor),
    declare_binary_operator_primitive!("mod", wrapping_rem),
    declare_binary_operator_primitive!("lshift", shl),
    declare_binary_operator_primitive!("rshift", shr),
    declare_unary_operator_primitive!("negate", -),
    declare_unary_operator_primitive!("invert", !),
    declare_compare_operator_primitive!("=", ==),
    declare_compare_operator_primitive!("<", <),
    declare_compare_operator_primitive!(">", >),
    declare_primitive!(":", env, {
        let name = env.read_name_from_input_buffer().unwrap();
        env.dictionary.push_front(DictionaryEntry {
            name,
            immediate: false,
            body: Vec::new(),
        });
        env.currently_compiling = Flag::True as Cell;
    }),
    declare_primitive!("r>", env, {
        let calling_word_return_address = env.return_stack.pop().unwrap();
        let from_return_stack = env.return_stack.pop().unwrap();
        env.data_stack.push(from_return_stack as Cell).unwrap();
        env.return_stack.push(calling_word_return_address).unwrap();
    }),
    declare_primitive!(">r", env, {
        let calling_word_return_address = env.return_stack.pop().unwrap();
        let from_data_stack = env.data_stack.pop().unwrap();
        env.return_stack
            .push(from_data_stack as *const ForthOperation)
            .unwrap();
        env.return_stack.push(calling_word_return_address).unwrap();
    }),
    declare_primitive!("u.", env, {
        let s = env.data_stack.pop().unwrap();
        let u: usize = s as usize;
        env.print_number(u);
    }),
    declare_primitive!("u<", env, {
        let s2 = env.data_stack.pop().unwrap();
        let s1 = env.data_stack.pop().unwrap();
        let u2 = s2 as UCell;
        let u1 = s1 as UCell;
        let result: bool = u1 < u2;
        let result: Flag = result.into();
        env.data_stack.push(result as Cell).unwrap();
    }),
    declare_primitive!("move", env, {
        let length = env.data_stack.pop().unwrap() as usize;
        let dest = env.data_stack.pop().unwrap() as *mut Byte;
        let src = env.data_stack.pop().unwrap() as *const Byte;
        unsafe { std::ptr::copy(src, dest, length) };
    }),
    declare_primitive!("depth", env, {
        env.data_stack.push(env.data_stack.len() as Cell).unwrap();
    }),
    declare_primitive!("quit", env, {
        env.return_stack.clear();
        // TODO: Don't print ok after execution
    }),
    declare_primitive!(">in", env, {
        let address: *mut Cell = &mut env.input_buffer_head;
        let address = address as Cell;
        env.data_stack.push(address).unwrap();
    }),
    declare_primitive!("state", env, {
        let address: *mut Cell = &mut env.currently_compiling;
        let address = address as Cell;
        env.data_stack.push(address).unwrap();
    }),
    declare_primitive!("source", env, {
        let address = env.input_buffer.as_ptr() as Cell;
        let mut size: Cell = 0;
        while let Some(c) = env.input_buffer.get(size as usize) {
            if *c == 0 {
                break;
            }
            size += 1;
        }
        env.data_stack.push(address).unwrap();
        env.data_stack.push(size).unwrap();
    }),
    declare_primitive!("immediate", env, {
        env.latest_mut().immediate = true;
    }),
    declare_primitive!("word", env, {
        let delimiter = env.data_stack.pop().unwrap();
        let token = env.next_token(USUAL_LEADING_DELIMITERS_TO_IGNORE, delimiter as Byte);
        let token = token.to_owned(); // TODO: Copy into stack instead of heap (use alloca?)
        let token = unsafe { CountedString::from_slice(&token, env.parsed_word) }.unwrap();
        let token_address: *const CountedString = token;
        env.data_stack.push(token_address as Cell).unwrap();
    }),
    declare_primitive!("count", env, {
        let counted_string_address = env.data_stack.pop().unwrap();
        let counted_string: &CountedString =
            unsafe { (counted_string_address as *const CountedString).as_ref() }.unwrap();
        let address_of_first_character: *const Byte = counted_string.data.as_ptr();
        let byte_count = counted_string.len;

        env.data_stack
            .push(address_of_first_character as Cell)
            .unwrap();
        env.data_stack.push(byte_count as Cell).unwrap();
    }),
    declare_primitive!("'", env, {
        let name = env.read_name_from_input_buffer().unwrap();
        let entry = search_dictionary(&env.dictionary, &name).unwrap();
        let entry: *const DictionaryEntry = entry;
        env.data_stack.push(entry as Cell).unwrap();
    }),
    declare_primitive!("execute", env, {
        let entry = env.data_stack.pop().unwrap();
        let entry = entry as *const DictionaryEntry;
        let entry = unsafe { entry.as_ref() }.unwrap();
        env.execute_word(entry.body.first().unwrap());
    }),
    declare_primitive!(">body", env, {
        let entry = env.data_stack.pop().unwrap();
        let entry = entry as *const DictionaryEntry;
        let entry = unsafe { entry.as_ref() }.unwrap();
        match entry.body.first().unwrap() {
            ForthOperation::PushData(result) => env.data_stack.push(*result).unwrap(),
            _ => panic!("Invalid argument given to >body"),
        }
    }),
    declare_primitive!("find", env, {
        let name_address = env.data_stack.pop().unwrap();
        let name: &CountedString =
            unsafe { (name_address as *const CountedString).as_ref() }.unwrap();
        let name = Name::from_ascii(unsafe { name.as_slice() });
        match search_dictionary(&env.dictionary, &name) {
            Some(entry) => {
                let immediate = if entry.immediate { 1 } else { -1 };
                let entry: *const DictionaryEntry = entry;
                env.data_stack.push(entry as Cell).unwrap();
                env.data_stack.push(immediate).unwrap();
            }
            _ => {
                env.data_stack.push(name_address).unwrap();
                env.data_stack.push(0).unwrap();
            }
        }
    }),
    declare_primitive!("see", env, {
        let name = env.read_name_from_input_buffer().unwrap();
        let item = search_dictionary(&env.dictionary, &name).unwrap();
        println!("{}", item);
    }),
    declare_primitive!("abort", env, {
        env.data_stack.clear();

        // TODO: Call quit instead of copying code.
        env.return_stack.clear();
        // TODO: Don't print ok
    }),
    declare_constant!("MAX-CHAR", Byte::MAX),
    declare_constant!("ADDRESS-UNIT-BITS", Cell::BITS),
    declare_constant!("MAX-N", Cell::MAX),
    declare_constant!("MAX-U", UCell::MAX),
    declare_primitive!("MAX-D", env, {
        env.data_stack.push_double_cell(DoubleCell::MAX).unwrap()
    }),
    declare_primitive!("MAX-UD", env, {
        env.data_stack
            .push_double_cell(DoubleUCell::MAX as DoubleCell)
            .unwrap()
    }),
    declare_primitive!("evaluate", env, {
        let string_byte_count = env.data_stack.pop().unwrap() as usize;
        let string_address = env.data_stack.pop().unwrap();
        let string_address = string_address as *const u8;
        let string = unsafe { std::slice::from_raw_parts(string_address, string_byte_count) };
        let input_buffer_head_backup = env.input_buffer_head;
        let input_buffer_backup = env.input_buffer.to_vec();

        // TODO: Set the input buffer to be `string`, don't just copy it.
        env.interpret_line(string);

        env.input_buffer_head = input_buffer_head_backup;
        env.input_buffer.copy_from_slice(&input_buffer_backup);
    }),
    declare_primitive!("key", env, {
        let mut key_buffer: [Byte; 1] = [0; 1];
        std::io::stdin().read_exact(&mut key_buffer).unwrap();
        env.data_stack
            .push(*key_buffer.first().unwrap() as Cell)
            .unwrap();
    }),
    declare_primitive!("accept", env, {
        let max_length = env.data_stack.pop().unwrap();
        let max_length = max_length as usize;
        let destination = env.data_stack.pop().unwrap();
        let destination = destination as *mut Byte;
        let buffer = unsafe { std::slice::from_raw_parts_mut(destination, max_length) };
        std::io::stdin().read_exact(buffer).unwrap();
    }),
    declare_primitive!("m*", env, {
        let x = env.data_stack.pop().unwrap();
        let y = env.data_stack.pop().unwrap();
        let result: DoubleCell = (x as DoubleCell) * (y as DoubleCell);
        env.data_stack.push_double_cell(result).unwrap();
    }),
    declare_primitive!("sm/rem", env, {
        let divisor: Cell = env.data_stack.pop().unwrap();
        let divided: DoubleCell = env.data_stack.pop_double_cell().unwrap();

        let divisor = divisor as DoubleCell;
        let quotient = (divided / divisor) as Cell;
        let remainder = (divided % divisor) as Cell;

        env.data_stack.push(remainder).unwrap();
        env.data_stack.push(quotient).unwrap();
    }),
    declare_immediate_primitive!(";", env, {
        env.latest_mut().body.push(ForthOperation::Return);
        env.currently_compiling = Flag::False as Cell;
    }),
    declare_primitive!("latest-push", env, {
        let x = env.data_stack.pop_double_cell().unwrap();
        let op = ForthOperation::try_from(x).unwrap();
        env.latest_mut().body.push(op);
    }),
    declare_primitive!("latest-len", env, {
        env.data_stack
            .push(env.latest().body.len() as UCell as Cell)
            .unwrap();
    }),
    declare_primitive!("latest!", env, {
        let index = env.data_stack.pop().unwrap() as UCell;
        let op = ForthOperation::try_from(env.data_stack.pop_double_cell().unwrap()).unwrap();
        *env.latest_mut().body.get_mut(index).unwrap() = op;
    }),
    declare_primitive!("latest-last-unres-if-or-else", env, {
        let unresolved_if_branch_index = env
            .reverse_find_in_latest(|item| {
                matches!(
                    item,
                    ForthOperation::Unresolved(UnresolvedOperation::If | UnresolvedOperation::Else)
                )
            })
            .unwrap();
        env.data_stack
            .push(unresolved_if_branch_index as UCell as Cell)
            .unwrap();
    }),
    declare_primitive!("latest-last-unres-while", env, {
        let unresolved_if_branch_index = env
            .reverse_find_in_latest(|item| {
                matches!(item, ForthOperation::Unresolved(UnresolvedOperation::While))
            })
            .unwrap();
        env.data_stack
            .push(unresolved_if_branch_index as UCell as Cell)
            .unwrap();
    }),
    declare_primitive!("cf>", env, {
        env.data_stack
            .push(env.control_flow_stack.pop().unwrap().try_into().unwrap())
            .unwrap();
    }),
    declare_primitive!(">cf", env, {
        env.control_flow_stack
            .push(env.data_stack.pop().unwrap().try_into().unwrap())
            .unwrap();
    }),
    declare_immediate_primitive!("postpone", env, {
        let name = env.read_name_from_input_buffer().unwrap();
        let entry = search_dictionary(&env.dictionary, &name).unwrap();
        let operation = ForthOperation::CallEntry(entry);
        env.latest_mut().body.push(operation);
    }),
    declare_immediate_primitive!("(", env, {
        env.next_token(&[], b')');
    }),
    declare_immediate_primitive!("\\", env, {
        env.input_buffer_head = env.input_buffer.len() as Cell;
    }),
    declare_immediate_primitive!("s\"", env, {
        let string = env.next_token(&[], b'"').to_owned(); // TODO: Possible without copying to heap?
        let length = string.len();

        // Copy to data space
        let data_space_string = env.data_space_manager.allot(length).unwrap();
        data_space_string.copy_from_slice(&string);
        let data_space_string_address = data_space_string.as_ptr();

        if env.compile_mode() {
            env.latest_mut().body.append(&mut vec![
                ForthOperation::PushData(data_space_string_address as Cell),
                ForthOperation::PushData(length as Cell),
            ]);
        } else {
            env.data_stack
                .push(data_space_string_address as Cell)
                .unwrap();
            env.data_stack.push(length as Cell).unwrap();
        }
    }),
    declare_immediate_primitive!("recurse", env, {
        let latest = env.latest_mut();
        let call_self = ForthOperation::CallEntry(latest);
        latest.body.push(call_self);
    }),
    declare_primitive!("cl>", env, {
        env.data_stack
            .push_double_cell(env.counted_loop_stack.pop().unwrap().into())
            .unwrap();
    }),
    declare_primitive!(">cl", env, {
        env.counted_loop_stack
            .push(env.data_stack.pop_double_cell().unwrap().into())
            .unwrap();
    }),
    declare_immediate_primitive!("+loop", env, {
        if env.compile_mode() {
            // Append the `else` section of this implementation
            env.latest_mut()
                .body
                .push(ForthOperation::CallPrimitive(get_primitive!("+loop")));

            let loop_start_index = env.control_flow_stack.pop().unwrap();
            let loop_operation_count = env.latest_mut().body.len() - loop_start_index;

            // Append the jump back to the beginning of the do loop
            env.latest_mut().body.push(ForthOperation::BranchOnFalse(
                -(Cell::try_from(loop_operation_count).unwrap()),
            ));

            // Resolve all the `UnresolvedOperation::Leave` in the do loop
            let after_loop_index = env.latest().body.len();
            for index in loop_start_index..env.latest().body.len() {
                let item = env.latest_mut().body.get_mut(index).unwrap();
                if let ForthOperation::Unresolved(UnresolvedOperation::Leave) = item {
                    let amount_to_advance_to_exit_the_loop = after_loop_index - index;
                    *item = ForthOperation::BranchOnFalse(
                        isize::try_from(amount_to_advance_to_exit_the_loop).unwrap(),
                    );
                }
            }
        } else {
            let mut loop_state = env.counted_loop_stack.pop().unwrap();
            let addition = env.data_stack.pop().unwrap();
            loop_state.loop_counter += addition;
            if loop_state.loop_counter >= loop_state.limit {
                env.data_stack.push(Flag::True as Cell).unwrap(); // Jump back to the start of the do loop
            } else {
                env.counted_loop_stack.push(loop_state).unwrap();
                env.data_stack.push(Flag::False as Cell).unwrap(); // Loop is done, continue
            }

            // The next instruction is BranchOnFalse
        }
    }),
    declare_primitive!("syscall", env, {
        if cfg!(all(target_arch = "x86_64", target_os = "linux")) {
            let arg6: u64 = env.data_stack.pop().unwrap() as u64;
            let arg5: u64 = env.data_stack.pop().unwrap() as u64;
            let arg4: u64 = env.data_stack.pop().unwrap() as u64;
            let arg3: u64 = env.data_stack.pop().unwrap() as u64;
            let arg2: u64 = env.data_stack.pop().unwrap() as u64;
            let arg1: u64 = env.data_stack.pop().unwrap() as u64;
            let syscall_number: u64 = env.data_stack.pop().unwrap() as u64;
            let return_value1: u64;
            let return_value2: u64;

            unsafe {
                core::arch::asm!("syscall",
				 // https://www.man7.org/linux/man-pages/man2/syscall.2.html
                                 in("rax") syscall_number,
                                 in("rdi") arg1,
                                 in("rsi") arg2,
                                 in("rdx") arg3,
                                 in("r10") arg4,
                                 in("r8") arg5,
                                 in("r9") arg6,
				 lateout("rax") return_value1,
				 lateout("rdx") return_value2,
                                 // These are clobbered by `syscall` (https://www.felixcloutier.com/x86/syscall)
                                 out("rcx") _,
                                 out("r11") _);
            };

            env.data_stack.push(return_value1 as Cell).unwrap();
            env.data_stack.push(return_value2 as Cell).unwrap();
        } else {
            panic!("Not implemented for this platform");
        }
    }),
];

const FORTH_RUNTIME_INIT: &str = include_str!(concat!(env!("OUT_DIR"), "/runtime.fth"));

fn search_dictionary<'a>(dict: &'a Dictionary, name: &Name) -> Option<&'a DictionaryEntry> {
    dict.iter().find(|&item| item.name == *name)
}

fn parse_number(default_base: u32, word: &str) -> Option<Cell> {
    if word.is_empty() {
        return None;
    }

    let mut has_base_indicator = true;
    let base = match word.as_bytes().first()? {
        b'#' => 10,
        b'$' => 16,
        b'%' => 2,
        _ => {
            has_base_indicator = false;
            default_base
        }
    };

    let digits = word.split_at(if has_base_indicator { 1 } else { 0 }).1;

    match Cell::from_str_radix(digits, base) {
        Ok(x) => Some(x),
        _ => None,
    }
}

impl<'a> Environment<'a> {
    fn new(
        data_space: &'a mut [Byte],
        input_buffer_byte_count: usize,
        parsed_word_buffer_byte_count: usize,
        data_stack_byte_count: usize,
        return_stack_byte_count: usize,
        control_flow_stack_byte_count: usize,
        counted_loop_stack_byte_count: usize,
    ) -> Option<Environment<'a>> {
        let mut data_space_manager = DataSpaceManager::new(data_space);
        let input_buffer = data_space_manager.allot(input_buffer_byte_count)?;
        let parsed_word = data_space_manager.allot(parsed_word_buffer_byte_count)?;
        let data_stack_buffer = data_space_manager.allot(data_stack_byte_count)?;
        let return_stack_buffer = data_space_manager.allot(return_stack_byte_count)?;
        let control_flow_stack_buffer = data_space_manager.allot(control_flow_stack_byte_count)?;
        let counted_loop_stack_buffer = data_space_manager.allot(counted_loop_stack_byte_count)?;

        fn stack_from_byte_slice<'a, T>(slice: &'a mut [Byte]) -> Stack<'a, T>
        where
            T: Copy,
        {
            let x: &'a mut [T] = unsafe {
                std::slice::from_raw_parts_mut(
                    slice.as_mut_ptr() as *mut T,
                    slice.len() / std::mem::size_of::<T>(),
                )
            };

            Stack::new(x)
        }

        let data_stack = stack_from_byte_slice(data_stack_buffer);
        let return_stack = stack_from_byte_slice(return_stack_buffer);
        let control_flow_stack = stack_from_byte_slice(control_flow_stack_buffer);
        let counted_loop_stack = stack_from_byte_slice(counted_loop_stack_buffer);

        let dictionary =
            std::collections::LinkedList::from_iter(STATIC_DICTIONARY.iter().map(|static_entry| {
                DictionaryEntry {
                    name: Name::from_ascii(static_entry.name.as_bytes()),
                    immediate: static_entry.immediate,
                    body: vec![static_entry.body.clone(), ForthOperation::Return],
                }
            }));

        let mut result = Environment {
            data_space_manager,
            data_stack,
            return_stack,
            input_buffer,
            input_buffer_head: 0,
            dictionary,
            base: 10,
            currently_compiling: Flag::False as Cell,
            control_flow_stack,
            parsed_word,
            counted_loop_stack,
        };

        for line in FORTH_RUNTIME_INIT.lines() {
            result.interpret_line(line.as_bytes());
        }

        Some(result)
    }

    fn new_default_sized(data_space: &'a mut [Byte]) -> Option<Environment<'a>> {
        Environment::new(
            data_space,
            1024,
            1024,
            100 * std::mem::size_of::<Cell>(),
            100 * std::mem::size_of::<*const ForthOperation>(),
            100 * std::mem::size_of::<UCell>(),
            100 * std::mem::size_of::<CountedLoopState>(),
        )
    }

    fn compile_mode(&self) -> bool {
        self.currently_compiling == Flag::True as Cell
    }

    fn latest(&self) -> &DictionaryEntry {
        self.dictionary.front().unwrap()
    }

    fn latest_mut(&mut self) -> &mut DictionaryEntry {
        self.dictionary.front_mut().unwrap()
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
                    return &[];
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

        &self.input_buffer[token_begin..token_begin + token_size]
    }

    fn interpret_line(&mut self, line: &[Byte]) {
        if line.is_empty() {
            return;
        }

        // Reset input buffer
        self.input_buffer_head = 0;
        self.input_buffer[0..line.len()].copy_from_slice(line);
        self.input_buffer[line.len()..].fill(0);

        'empty_input_buffer: loop {
            let token = self.next_token(USUAL_LEADING_DELIMITERS_TO_IGNORE, b' ');

            if token.is_empty() {
                break 'empty_input_buffer;
            }

            let token: String = String::from_utf8_lossy(token).to_string();

            self.handle_token(&token);
        }
    }

    fn handle_token(&mut self, token: &str) {
        match parse_number(self.base as u32, token) {
            Some(number) => self.handle_number_token(number),
            _ => self.handle_text_token(token),
        }
    }

    fn handle_number_token(&mut self, token: Cell) {
        if self.compile_mode() {
            let literal = ForthOperation::PushData(token);
            self.latest_mut().body.push(literal);
        } else {
            self.data_stack.push(token).unwrap();
        }
    }

    fn handle_text_token(&mut self, token: &str) {
        let dict_entry =
            search_dictionary(&self.dictionary, &Name::from_ascii(token.as_bytes())).unwrap();

        if self.compile_mode() && !dict_entry.immediate {
            let operation = ForthOperation::CallEntry(dict_entry);
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
                ForthOperation::CallEntry(w) => {
                    let w = unsafe { w.as_ref() }.unwrap();
                    let to_execute = &w.body;

                    let next = unsafe { instruction_pointer.add(1) };
                    self.return_stack.push(next).unwrap();
                    instruction_pointer = to_execute.first().unwrap();
                    continue;
                }
                ForthOperation::PushData(l) => self.data_stack.push(*l).unwrap(),
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

    fn reverse_find_in_latest<F>(&self, test: F) -> Option<usize>
    where
        F: Fn(&ForthOperation) -> bool,
    {
        self.latest()
            .body
            .iter()
            .enumerate()
            .rev()
            .find(|(_, operation)| test(operation))
            .map(|(index, _)| index)
    }

    fn read_name_from_input_buffer(&mut self) -> Option<Name> {
        let name = self.next_token(USUAL_LEADING_DELIMITERS_TO_IGNORE, b' ');
        if name.is_empty() {
            return None;
        }

        Some(Name::from_ascii(name))
    }
}

/// Create a static environment
macro_rules! default_fixed_sized_environment {
    ($name:ident) => {
        let mut data_space = [0; 10 * 1024];
        let mut $name = Environment::new_default_sized(&mut data_space).unwrap();
    };
}

fn main() {
    default_fixed_sized_environment!(environment);
    loop {
        let mut line_buffer = String::new();
        std::io::stdin().read_line(&mut line_buffer).unwrap();
        line_buffer.pop();
        environment.interpret_line(line_buffer.as_bytes());
        println!(" ok. ");
        std::io::stdout().flush().unwrap();
    }
}

#[cfg(test)]
mod tests;

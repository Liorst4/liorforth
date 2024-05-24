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

use std::io::{IsTerminal, Read, Write};
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

#[derive(Debug, Clone, PartialEq)]
enum SystemExceptionCode {
    StackOverflow,
    StackUnderflow,
    ReturnStackOverflow,
    ReturnStackUnderflow,
    CountedLoopsStackOverflow,
    DivisionByZero,
    UndefinedWord,
    ControlFlowStackOverflow,
}

impl SystemExceptionCode {
    const fn const_into(self) -> Cell {
        match self {
            SystemExceptionCode::StackOverflow => -3,
            SystemExceptionCode::StackUnderflow => -4,
            SystemExceptionCode::ReturnStackOverflow => -5,
            SystemExceptionCode::ReturnStackUnderflow => -6,
            SystemExceptionCode::CountedLoopsStackOverflow => -7,
            SystemExceptionCode::DivisionByZero => -10,
            SystemExceptionCode::UndefinedWord => -13,
            SystemExceptionCode::ControlFlowStackOverflow => -52,
        }
    }
}

impl From<SystemExceptionCode> for Cell {
    fn from(code: SystemExceptionCode) -> Cell {
        code.const_into()
    }
}

#[derive(Debug, Clone, PartialEq)]
#[repr(packed(1), C)]
struct Exception {
    value: Cell,
}

impl From<Cell> for Exception {
    fn from(c: Cell) -> Exception {
        Exception { value: c }
    }
}

impl From<SystemExceptionCode> for Exception {
    fn from(code: SystemExceptionCode) -> Exception {
        Exception { value: code.into() }
    }
}

struct Stack<
    'a,
    T,
    const OVERFLOW_ERROR_CODE: Cell = { SystemExceptionCode::StackOverflow.const_into() },
    const UNDERFLOW_ERROR_CODE: Cell = { SystemExceptionCode::StackUnderflow.const_into() },
> where
    T: Copy,
{
    head: usize,
    data: &'a mut [T],
}

impl<'a, T, const OVERFLOW_ERROR_CODE: Cell, const UNDERFLOW_ERROR_CODE: Cell>
    Stack<'a, T, OVERFLOW_ERROR_CODE, UNDERFLOW_ERROR_CODE>
where
    T: Copy,
{
    fn new(data: &'a mut [T]) -> Stack<'a, T, OVERFLOW_ERROR_CODE, UNDERFLOW_ERROR_CODE> {
        Stack { head: 0, data }
    }

    fn push(&mut self, x: T) -> Result<(), Exception> {
        if self.head >= self.data.len() {
            return Err(Exception::from(OVERFLOW_ERROR_CODE));
        }

        self.data[self.head] = x;
        self.head += 1;

        Ok(())
    }

    fn pop(&mut self) -> Result<T, Exception> {
        if self.head == 0 {
            return Err(Exception::from(UNDERFLOW_ERROR_CODE));
        }

        let result = self.data[self.head - 1];
        self.head -= 1;

        Ok(result)
    }

    fn last(&self) -> Result<&T, Exception> {
        if self.head == 0 {
            return Err(Exception::from(UNDERFLOW_ERROR_CODE));
        }

        Ok(&self.data[self.head - 1])
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

    #[allow(unused)]
    fn as_slice(&self) -> &[T] {
        &self.data[0..self.head]
    }

    fn backup(&self) -> Vec<T> {
        if self.head == 0 {
            return vec![];
        }

        self.data[0..self.head].to_owned()
    }

    fn restore(&mut self, backup: &Vec<T>) {
        if backup.is_empty() {
            self.head = 0;
            return;
        }

        self.head = backup.len();
        self.data[0..self.head].copy_from_slice(backup);
    }
}

impl<'a, const OVERFLOW_ERROR_CODE: Cell, const UNDERFLOW_ERROR_CODE: Cell>
    Stack<'a, Cell, OVERFLOW_ERROR_CODE, UNDERFLOW_ERROR_CODE>
{
    fn push_double_cell(&mut self, value: DoubleCell) -> Result<(), Exception> {
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

    fn pop_double_cell(&mut self) -> Result<DoubleCell, Exception> {
        if self.len() < 2 {
            return Err(Exception::from(UNDERFLOW_ERROR_CODE));
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
type Primitive = fn(&mut Environment) -> Result<(), Exception>;

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
            ForthOperation::PushData(literal) => write!(f, "PUSH-DATA\t{}", literal),
            ForthOperation::CallEntry(another_entry) => {
                let another_entry_addr = *another_entry as usize;
                let name = &unsafe { another_entry.as_ref() }.unwrap().name;
                write!(
                    f,
                    "CALL-ENTRY\t${:x}\t({})",
                    another_entry_addr,
                    name.as_str().unwrap()
                )
            }
            ForthOperation::BranchOnFalse(offset) => {
                let byte_offset = offset * (std::mem::size_of::<ForthOperation>() as isize);
                let dest: usize = ((address as isize) + byte_offset) as usize;
                write!(f, "BRANCH-ON-FALSE\t{}\t(${:x})", offset, dest)
            }
            ForthOperation::Branch(destination) => {
                let destination_address = *destination as Cell;
                write!(f, "BRANCH\t${:x}", destination_address)
            }
            ForthOperation::CallPrimitive(primitive) => {
                let primitive: usize = unsafe { std::mem::transmute(primitive) };
                write!(f, "CALL-PRIMITIVE\t${:x}", primitive)
            }
            ForthOperation::Return => write!(f, "RETURN"),
            ForthOperation::Unresolved(x) => write!(f, "UNRESOLVED\t{:?}", x),
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
    return_stack: Stack<
        'a,
        *const ForthOperation,
        { SystemExceptionCode::ReturnStackOverflow.const_into() },
        { SystemExceptionCode::ReturnStackUnderflow.const_into() },
    >,

    input_buffer: &'a mut [Byte],
    input_buffer_head: Cell,

    dictionary: Dictionary,

    base: Cell,

    currently_compiling: Cell,
    control_flow_stack:
        Stack<'a, UCell, { SystemExceptionCode::ControlFlowStackOverflow.const_into() }>,

    parsed_word: &'a mut [Byte],

    counted_loop_stack: Stack<
        'a,
        CountedLoopState,
        { SystemExceptionCode::CountedLoopsStackOverflow.const_into() },
    >,
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
                fn primitive($arg: &mut Environment) -> Result<(), Exception>{
                    $body
                    Ok(())
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
            let b = env.data_stack.pop()?;
            let a = env.data_stack.pop()?;
            let c = a.$method(b);
            env.data_stack.push(c)?;
        })
    };
}

macro_rules! declare_unary_operator_primitive {
    ($name:literal, $operator:tt) => {
	declare_primitive!($name, env, {
            let a = env.data_stack.pop()?;
	    let b = $operator a;
            env.data_stack.push(b)?;
	})
    };
}

macro_rules! declare_compare_operator_primitive {
    ($name:literal, $operator:tt) => {
	declare_primitive!($name, env, {
            let b = env.data_stack.pop()?;
            let a = env.data_stack.pop()?;
            let c = a $operator b;
	    let f : Flag = c.into();
            env.data_stack.push(f as Cell)?;
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
        let x = *env.data_stack.last()?;
        env.data_stack.push(x)?;
    }),
    declare_primitive!("drop", env, {
        env.data_stack.pop()?;
    }),
    declare_primitive!(".", env, {
        let x = env.data_stack.pop()?;
        env.print_number(x);
    }),
    declare_primitive!("swap", env, {
        let a = env.data_stack.pop()?;
        let b = env.data_stack.pop()?;
        env.data_stack.push(a)?;
        env.data_stack.push(b)?;
    }),
    declare_primitive!("over", env, {
        let a = env.data_stack.pop()?;
        let b = env.data_stack.pop()?;
        env.data_stack.push(b)?;
        env.data_stack.push(a)?;
        env.data_stack.push(b)?;
    }),
    declare_primitive!("rot", env, {
        let a = env.data_stack.pop()?;
        let b = env.data_stack.pop()?;
        let c = env.data_stack.pop()?;
        env.data_stack.push(b)?;
        env.data_stack.push(a)?;
        env.data_stack.push(c)?;
    }),
    declare_primitive!("/mod", env, {
        let divisor = env.data_stack.pop()?;
        if divisor == 0 {
            return Err(SystemExceptionCode::DivisionByZero.into());
        }

        let divided = env.data_stack.pop()?;
        let remainder = divided % divisor;
        let quotient = divided / divisor;
        env.data_stack.push(remainder)?;
        env.data_stack.push(quotient)?;
    }),
    declare_primitive!("here", env, {
        let address: *mut Byte = unsafe { env.data_space_manager.here() };
        env.data_stack.push(address as Cell)?;
    }),
    declare_primitive!("allot", env, {
        let n = env.data_stack.pop()?;
        if n > 0 {
            env.data_space_manager
                .allot(n as usize)
                .expect("Not enough memory");
        }
    }),
    declare_primitive!("@", env, {
        let n = env.data_stack.pop()?;
        let address = n as *mut Cell;
        let data = unsafe { std::ptr::read_unaligned::<Cell>(address) };
        env.data_stack.push(data)?;
    }),
    declare_primitive!("!", env, {
        let n = env.data_stack.pop()?;
        let data = env.data_stack.pop()?;
        let address = n as *mut Cell;
        unsafe { std::ptr::write_unaligned(address, data) };
    }),
    declare_primitive!("c@", env, {
        let n = env.data_stack.pop()?;
        let address = n as *mut Byte;
        let data = unsafe { std::ptr::read_unaligned::<Byte>(address) };
        env.data_stack.push(data as Cell)?;
    }),
    declare_primitive!("c!", env, {
        let n = env.data_stack.pop()?;
        let data = env.data_stack.pop()? as Byte;
        let address = n as *mut Byte;
        unsafe { std::ptr::write_unaligned(address, data) };
    }),
    declare_primitive!("emit", env, {
        let n = env.data_stack.pop()?;
        let c = (n as u8) as char;
        print!("{}", c);
    }),
    declare_primitive!("base", env, {
        let base_address: *mut Cell = &mut env.base;
        env.data_stack.push(base_address as Cell)?;
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
        let calling_word_return_address = env.return_stack.pop()?;
        let from_return_stack = env.return_stack.pop()?;
        env.data_stack.push(from_return_stack as Cell)?;
        env.return_stack.push(calling_word_return_address)?;
    }),
    declare_primitive!(">r", env, {
        let calling_word_return_address = env.return_stack.pop()?;
        let from_data_stack = env.data_stack.pop()?;
        env.return_stack
            .push(from_data_stack as *const ForthOperation)?;
        env.return_stack.push(calling_word_return_address)?;
    }),
    declare_primitive!("u.", env, {
        let s = env.data_stack.pop()?;
        let u: usize = s as usize;
        env.print_number(u);
    }),
    declare_primitive!("u<", env, {
        let s2 = env.data_stack.pop()?;
        let s1 = env.data_stack.pop()?;
        let u2 = s2 as UCell;
        let u1 = s1 as UCell;
        let result: bool = u1 < u2;
        let result: Flag = result.into();
        env.data_stack.push(result as Cell)?;
    }),
    declare_primitive!("move", env, {
        let length = env.data_stack.pop()? as usize;
        let dest = env.data_stack.pop()? as *mut Byte;
        let src = env.data_stack.pop()? as *const Byte;
        unsafe { std::ptr::copy(src, dest, length) };
    }),
    declare_primitive!("depth", env, {
        env.data_stack.push(env.data_stack.len() as Cell)?;
    }),
    declare_primitive!("quit", env, {
        env.return_stack.clear();
        // TODO: Don't print ok after execution
    }),
    declare_primitive!(">in", env, {
        let address: *mut Cell = &mut env.input_buffer_head;
        let address = address as Cell;
        env.data_stack.push(address)?;
    }),
    declare_primitive!("state", env, {
        let address: *mut Cell = &mut env.currently_compiling;
        let address = address as Cell;
        env.data_stack.push(address)?;
    }),
    declare_primitive!("source", env, {
        let address = env.input_buffer.as_ptr() as Cell;
        let size = env.input_buffer.iter().take_while(|c| **c != 0).count() as Cell;
        env.data_stack.push(address)?;
        env.data_stack.push(size)?;
    }),
    declare_primitive!("immediate", env, {
        env.latest_mut().immediate = true;
    }),
    declare_primitive!("word", env, {
        let delimiter = env.data_stack.pop()?;
        let token = env.next_token(USUAL_LEADING_DELIMITERS_TO_IGNORE, delimiter as Byte);
        let token = token.to_owned(); // TODO: Copy into stack instead of heap (use alloca?)
        let token = unsafe { CountedString::from_slice(&token, env.parsed_word) }.unwrap();
        let token_address: *const CountedString = token;
        env.data_stack.push(token_address as Cell)?;
    }),
    declare_primitive!("count", env, {
        let counted_string_address = env.data_stack.pop()?;
        let counted_string: &CountedString =
            unsafe { (counted_string_address as *const CountedString).as_ref() }.unwrap();
        let address_of_first_character: *const Byte = counted_string.data.as_ptr();
        let byte_count = counted_string.len;

        env.data_stack.push(address_of_first_character as Cell)?;
        env.data_stack.push(byte_count as Cell)?;
    }),
    declare_primitive!("'", env, {
        let name = env.read_name_from_input_buffer().unwrap();
        let entry = search_dictionary(&env.dictionary, &name)?;
        let entry: *const DictionaryEntry = entry;
        env.data_stack.push(entry as Cell).unwrap();
    }),
    declare_primitive!("execute", env, {
        let entry = env.data_stack.pop()?;
        let entry = entry as *const DictionaryEntry;
        let entry = unsafe { entry.as_ref() }.unwrap();
        env.execute_word(entry.body.first().unwrap())?;
    }),
    declare_primitive!(">body", env, {
        let entry = env.data_stack.pop()?;
        let entry = entry as *const DictionaryEntry;
        let entry = unsafe { entry.as_ref() }.unwrap();
        match entry.body.first().unwrap() {
            ForthOperation::PushData(result) => env.data_stack.push(*result).unwrap(),
            _ => panic!("Invalid argument given to >body"),
        }
    }),
    declare_primitive!("find", env, {
        let name_address = env.data_stack.pop()?;
        let name: &CountedString =
            unsafe { (name_address as *const CountedString).as_ref() }.unwrap();
        let name = Name::from_ascii(unsafe { name.as_slice() });
        match search_dictionary(&env.dictionary, &name) {
            Ok(entry) => {
                let immediate = if entry.immediate { 1 } else { -1 };
                let entry: *const DictionaryEntry = entry;
                env.data_stack.push(entry as Cell)?;
                env.data_stack.push(immediate)?;
            }
            _ => {
                env.data_stack.push(name_address)?;
                env.data_stack.push(0)?;
            }
        }
    }),
    declare_primitive!("see", env, {
        let name = env.read_name_from_input_buffer().unwrap();
        let item = search_dictionary(&env.dictionary, &name)?;
        println!("{}", item);
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
        let string_byte_count = env.data_stack.pop()? as usize;
        let string_address = env.data_stack.pop()?;
        let string_address = string_address as *const u8;
        let string = unsafe { std::slice::from_raw_parts(string_address, string_byte_count) };

        // TODO: Code duplication with catch/throw?
        let input_buffer_head_backup = env.input_buffer_head;
        let input_buffer_backup = env.input_buffer.to_vec();

        // TODO: Set the input buffer to be `string`, don't just copy it.
        let result = env.interpret_line(string);

        // TODO: Code duplication with catch/throw?
        env.input_buffer_head = input_buffer_head_backup;
        env.input_buffer.copy_from_slice(&input_buffer_backup);

        result?; // TODO: Correct?
    }),
    declare_primitive!("key", env, {
        let mut key_buffer: [Byte; 1] = [0; 1];
        std::io::stdin().read_exact(&mut key_buffer).unwrap();
        env.data_stack.push(*key_buffer.first().unwrap() as Cell)?;
    }),
    declare_primitive!("accept", env, {
        let max_length = env.data_stack.pop()?;
        let max_length = max_length as usize;
        let destination = env.data_stack.pop()?;
        let destination = destination as *mut Byte;
        let buffer = unsafe { std::slice::from_raw_parts_mut(destination, max_length) };
        std::io::stdin().read_exact(buffer).unwrap();
    }),
    declare_primitive!("m*", env, {
        let x = env.data_stack.pop()?;
        let y = env.data_stack.pop()?;
        let result: DoubleCell = (x as DoubleCell) * (y as DoubleCell);
        env.data_stack.push_double_cell(result)?;
    }),
    declare_primitive!("sm/rem", env, {
        let divisor: Cell = env.data_stack.pop()?;
        if divisor == 0 {
            return Err(SystemExceptionCode::DivisionByZero.into());
        }

        let divided: DoubleCell = env.data_stack.pop_double_cell()?;

        let divisor = divisor as DoubleCell;
        let quotient = (divided / divisor) as Cell;
        let remainder = (divided % divisor) as Cell;

        env.data_stack.push(remainder)?;
        env.data_stack.push(quotient)?;
    }),
    declare_immediate_primitive!(";", env, {
        env.latest_mut().body.push(ForthOperation::Return);
        env.currently_compiling = Flag::False as Cell;
    }),
    declare_primitive!("latest-push", env, {
        let x = env.data_stack.pop_double_cell()?;
        let op = ForthOperation::try_from(x).unwrap();
        env.latest_mut().body.push(op);
    }),
    declare_primitive!("latest-len", env, {
        env.data_stack
            .push(env.latest().body.len() as UCell as Cell)?;
    }),
    declare_primitive!("latest!", env, {
        let index = env.data_stack.pop()? as UCell;
        let op = ForthOperation::try_from(env.data_stack.pop_double_cell()?).unwrap();
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
            .push(unresolved_if_branch_index as UCell as Cell)?;
    }),
    declare_primitive!("latest-last-unres-while", env, {
        let unresolved_if_branch_index = env
            .reverse_find_in_latest(|item| {
                matches!(item, ForthOperation::Unresolved(UnresolvedOperation::While))
            })
            .unwrap();
        env.data_stack
            .push(unresolved_if_branch_index as UCell as Cell)?;
    }),
    declare_primitive!("cf>", env, {
        env.data_stack
            .push(env.control_flow_stack.pop()?.try_into().unwrap())?;
    }),
    declare_primitive!(">cf", env, {
        env.control_flow_stack
            .push(env.data_stack.pop()?.try_into().unwrap())?;
    }),
    declare_immediate_primitive!("postpone", env, {
        let name = env.read_name_from_input_buffer().unwrap();
        let entry = search_dictionary(&env.dictionary, &name)?; // TODO: Throw invalid postpone instead?
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
            env.data_stack.push(data_space_string_address as Cell)?;
            env.data_stack.push(length as Cell)?;
        }
    }),
    declare_immediate_primitive!("recurse", env, {
        let latest = env.latest_mut();
        let call_self = ForthOperation::CallEntry(latest);
        latest.body.push(call_self);
    }),
    declare_primitive!("cl>", env, {
        env.data_stack
            .push_double_cell(env.counted_loop_stack.pop()?.into())?;
    }),
    declare_primitive!(">cl", env, {
        env.counted_loop_stack
            .push(env.data_stack.pop_double_cell().unwrap().into())?;
    }),
    declare_immediate_primitive!("+loop", env, {
        if env.compile_mode() {
            // Append the `else` section of this implementation
            env.latest_mut()
                .body
                .push(ForthOperation::CallPrimitive(get_primitive!("+loop")));

            let loop_start_index = env.control_flow_stack.pop()?;
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
            let mut loop_state = env.counted_loop_stack.pop()?;
            let addition = env.data_stack.pop()?;
            loop_state.loop_counter += addition;
            if loop_state.loop_counter >= loop_state.limit {
                env.data_stack.push(Flag::True as Cell)?; // Jump back to the start of the do loop
            } else {
                env.counted_loop_stack.push(loop_state)?;
                env.data_stack.push(Flag::False as Cell)?; // Loop is done, continue
            }

            // The next instruction is BranchOnFalse
        }
    }),
    #[cfg(all(target_arch = "x86_64", target_os = "linux"))]
    declare_primitive!("syscall", env, {
        let arg6: u64 = env.data_stack.pop()? as u64;
        let arg5: u64 = env.data_stack.pop()? as u64;
        let arg4: u64 = env.data_stack.pop()? as u64;
        let arg3: u64 = env.data_stack.pop()? as u64;
        let arg2: u64 = env.data_stack.pop()? as u64;
        let arg1: u64 = env.data_stack.pop()? as u64;
        let syscall_number: u64 = env.data_stack.pop()? as u64;
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

        env.data_stack.push(return_value1 as Cell)?;
        env.data_stack.push(return_value2 as Cell)?;
    }),
    declare_immediate_primitive!(".(", env, {
        let bytes = env.next_token(&[], b')');
        let string = core::str::from_utf8(bytes).unwrap();
        print!("{}", string);
    }),
    declare_primitive!(".R", env, {
        let alignment = env.data_stack.pop()?;
        let alignment: usize = if alignment < 0 { 0 } else { alignment as usize };
        let number = env.data_stack.pop()?;
        print!("{} ", env.format_number(number, alignment));
    }),
    declare_primitive!("U.R", env, {
        let alignment = env.data_stack.pop()?;
        let alignment: usize = if alignment < 0 { 0 } else { alignment as usize };
        let number = env.data_stack.pop()? as usize;
        print!("{} ", env.format_number(number, alignment));
    }),
    declare_primitive!("unused", env, {
        env.data_stack
            .push(env.data_space_manager.unused_area.len() as Cell)?;
    }),
    declare_primitive!("catch", env, {
        let execution_token = env.data_stack.pop()?;
        let entry = unsafe { (execution_token as *const DictionaryEntry).as_ref() }.unwrap();

        let input_buffer_head_backup = env.input_buffer_head;
        let input_buffer_backup = env.input_buffer.to_owned();

        let data_stack_backup = env.data_stack.backup();
        let return_stack_backup = env.return_stack.backup();
        let control_flow_stack_backup = env.control_flow_stack.backup();
        let counted_loop_stack_backup = env.counted_loop_stack.backup();

        let err = match env.execute_word(entry.body.as_ptr()) {
            Ok(_) => 0,
            Err(exception) => {
                env.data_stack.restore(&data_stack_backup);
                env.return_stack.restore(&return_stack_backup);
                env.control_flow_stack.restore(&control_flow_stack_backup);
                env.counted_loop_stack.restore(&counted_loop_stack_backup);

                env.input_buffer_head = input_buffer_head_backup;
                env.input_buffer.copy_from_slice(&input_buffer_backup);

                exception.value
            }
        };

        env.data_stack.push(err)?;
    }),
    declare_primitive!("throw", env, {
        let n = env.data_stack.pop()?;
        if n != 0 {
            return Err(Exception { value: n });
        }
    }),
];

const FORTH_RUNTIME_INIT: &str = include_str!(concat!(env!("OUT_DIR"), "/runtime.fth"));

fn search_dictionary<'a>(
    dict: &'a Dictionary,
    name: &Name,
) -> Result<&'a DictionaryEntry, Exception> {
    dict.iter()
        .find(|&item| item.name == *name)
        .ok_or(Exception::from(SystemExceptionCode::UndefinedWord))
}

fn parse_number(default_base: u32, word: &[Byte]) -> Option<Cell> {
    if word.is_empty() {
        return None;
    }

    let mut has_base_indicator = true;
    let base = match word.first()? {
        b'#' => 10,
        b'$' => 16,
        b'%' => 2,
        _ => {
            has_base_indicator = false;
            default_base
        }
    };

    let digits = word.split_at(if has_base_indicator { 1 } else { 0 }).1;

    match Cell::from_str_radix(core::str::from_utf8(digits).unwrap(), base) {
        Ok(x) => Some(x),
        Err(e) => match e.kind() {
            std::num::IntErrorKind::PosOverflow | std::num::IntErrorKind::NegOverflow => {
                panic!("number too long!")
            }
            _ => None,
        },
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

        fn stack_from_byte_slice<
            'a,
            T,
            const OVERFLOW_ERROR_CODE: Cell,
            const UNDERFLOW_ERROR_CODE: Cell,
        >(
            slice: &'a mut [Byte],
        ) -> Stack<'a, T, OVERFLOW_ERROR_CODE, UNDERFLOW_ERROR_CODE>
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
            result.interpret_line(line.as_bytes()).unwrap();
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
                    || self.input_buffer[self.input_buffer_head as usize] == 0
                {
                    return &[];
                }

                if !leading_delimiters.contains(&self.input_buffer[self.input_buffer_head as usize])
                {
                    break 'find_first_char;
                }

                self.input_buffer_head += 1;
            }
        }

        let token_begin = self.input_buffer_head as usize;
        let token_end;

        'read_token: loop {
            if self.input_buffer_head as usize >= self.input_buffer.len()
                || self.input_buffer[self.input_buffer_head as usize] == 0
            {
                token_end = self.input_buffer_head as usize;
                break 'read_token;
            }

            if self.input_buffer[self.input_buffer_head as usize] == delimiter {
                token_end = self.input_buffer_head as usize;
                self.input_buffer_head += 1;
                break 'read_token;
            }

            self.input_buffer_head += 1;
        }

        &self.input_buffer[token_begin..token_end]
    }

    fn interpret_line(&mut self, line: &[Byte]) -> Result<(), Exception> {
        if line.is_empty() {
            return Ok(());
        }

        // Reset input buffer
        self.input_buffer_head = 0;
        self.input_buffer[0..line.len()].copy_from_slice(line);
        self.input_buffer[line.len()..].fill(0);

        'empty_input_buffer: loop {
            let token = self
                .next_token(USUAL_LEADING_DELIMITERS_TO_IGNORE, b' ')
                .to_owned();

            if token.is_empty() {
                break 'empty_input_buffer;
            }

            self.handle_token(&token)?;
        }

        return Ok(());
    }

    fn handle_token(&mut self, token: &[Byte]) -> Result<(), Exception> {
        match parse_number(self.base as u32, token) {
            Some(number) => {
                self.handle_number_token(number);
                Ok(())
            }
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

    fn handle_text_token(&mut self, token: &[Byte]) -> Result<(), Exception> {
        let dict_entry = search_dictionary(&self.dictionary, &Name::from_ascii(token))?;

        if self.compile_mode() && !dict_entry.immediate {
            let operation = ForthOperation::CallEntry(dict_entry);
            self.latest_mut().body.push(operation);
            Ok(())
        } else {
            let next_word = &dict_entry.body;
            self.execute_word(next_word.first().unwrap())
        }
    }

    fn execute_word(&mut self, entry: *const ForthOperation) -> Result<(), Exception> {
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
                    let cond = self.data_stack.pop()?;
                    if cond == Flag::False as Cell {
                        instruction_pointer = unsafe { instruction_pointer.offset(*offset) };
                        continue;
                    }
                }
                ForthOperation::Branch(destination) => {
                    instruction_pointer = *destination;
                    continue;
                }
                ForthOperation::CallPrimitive(func) => func(self)?,
                ForthOperation::Return => match self.return_stack.len() {
                    0 => {
                        break; // Nothing left to execute
                    }
                    _ => {
                        instruction_pointer = self.return_stack.pop()?;
                        continue;
                    }
                },
                ForthOperation::Unresolved(_) => {
                    panic!("Unresolved branch!")
                }
            }

            instruction_pointer = unsafe { instruction_pointer.add(1) };
        }
        Ok(())
    }

    fn format_number<T: std::fmt::Binary + std::fmt::LowerHex + std::fmt::Display>(
        &self,
        n: T,
        alignment: usize,
    ) -> String {
        let mut result = match self.base {
            2 => format!("{:b}", n),
            16 => format!("{:x}", n),
            _ => format!("{}", n),
        };

        if result.len() < alignment {
            let spaces_to_add = alignment - result.len();
            result.reserve(spaces_to_add);
            for _ in 0..spaces_to_add {
                result.insert(0, ' ');
            }
        }

        result
    }

    fn print_number<T: std::fmt::Binary + std::fmt::LowerHex + std::fmt::Display>(&self, n: T) {
        print!("{} ", self.format_number(n, 0));
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
    let interactive = std::io::stdin().is_terminal();
    default_fixed_sized_environment!(environment);
    for maybe_line in std::io::stdin().lines() {
        match maybe_line {
            Ok(line) => {
                match environment.interpret_line(line.as_bytes()) {
                    Ok(_) => {
                        if interactive {
                            println!(" ok. ");
                        }
                    }
                    Err(exception) => {
                        eprintln!("{:?} was thrown", exception);
                        // TODO: Print stacks

                        if !interactive {
                            std::io::stdout().flush().unwrap();
                            std::io::stderr().flush().unwrap();
                            std::process::exit(1);
                        }

                        environment.data_stack.clear();
                        environment.return_stack.clear();
                        environment.control_flow_stack.clear();
                        environment.counted_loop_stack.clear();
                    }
                }

                std::io::stdout().flush().unwrap();
                std::io::stderr().flush().unwrap();
            }
            _ => break,
        }
    }
}

#[cfg(test)]
mod tests;

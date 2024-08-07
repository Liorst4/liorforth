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
use std::ops::{Add, BitAnd, BitOr, BitXor, Mul, Not, Shl, Shr};
use std::str::FromStr;

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

type Float = f32;

const fn align_to_float(addr: usize) -> usize {
    if addr % std::mem::size_of::<Float>() == 0 {
        return addr;
    }

    addr + (std::mem::size_of::<Float>() - (addr % std::mem::size_of::<Float>()))
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

#[cfg(target_pointer_width = "64")]
/// `UCell` with double the bits
type DoubleUCell = u128;

#[cfg(target_pointer_width = "32")]
/// `UCell` with double the bits
type DoubleUCell = u64;

#[cfg(target_pointer_width = "16")]
/// `UCell` with double the bits
type DoubleUCell = u32;

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

#[derive(Clone, PartialEq)]
struct Exception {
    value: Cell,
}

impl From<Cell> for Exception {
    fn from(c: Cell) -> Exception {
        Exception { value: c }
    }
}

macro_rules! declare_system_exception_codes {
    ( $(($value:literal, $name:ident)),+$(,)?) => {
	impl Exception {
	    $(
		const $name : Cell = $value;
	    )*
	}

	impl core::fmt::Debug for Exception {
	    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		let name: Option<_> = match self.value {
		    $(
			Exception::$name => Some(stringify!($name)),
		    )*
		    _ => None
		};

		match name {
		    Some(n) => write!(f, "{} ({})", self.value, n),
		    _ => write!(f, "{}", self.value)
		}
	    }
	}
    };
}

declare_system_exception_codes!(
    // Taken from https://forth-standard.org/standard/exception
    (-1, ABORT),
    (-2, QUOTATION_MARK_ABORT),
    (-3, STACK_OVERFLOW),
    (-4, STACK_UNDERFLOW),
    (-5, RETURN_STACK_OVERFLOW),
    (-6, RETURN_STACK_UNDERFLOW),
    (-7, DO_LOOPS_NESTED_TOO_DEEPLY_DURING_EXECUTION),
    // (-8, DICTIONARY_OVERFLOW),
    // (-9, INVALID_MEMORY_ADDRESS),
    (-10, DIVISION_BY_ZERO),
    // (-11, RESULT_OUT_OF_RANGE),
    // (-12, ARGUMENT_TYPE_MISMATCH),
    (-13, UNDEFINED_WORD),
    // (-14, INTERPRETING_A_COMPILE_ONLY_WORD),
    // (-15, INVALID_FORGET),
    (-16, ATTEMPT_TO_USE_ZERO_LENGTH_STRING_AS_A_NAME),
    // (-17, PICTURED_NUMERIC_OUTPUT_STRING_OVERFLOW),
    // (-18, PARSED_STRING_OVERFLOW),
    (-19, DEFINITION_NAME_TOO_LONG),
    // (-20, WRITE_TO_A_READ_ONLY_LOCATION),
    // (-21, UNSUPPORTED_OPERATION),
    // (-22, CONTROL_STRUCTURE_MISMATCH),
    // (-23, ADDRESS_ALIGNMENT_EXCEPTION),
    // (-24, INVALID_NUMERIC_ARGUMENT),
    // (-25, RETURN_STACK_IMBALANCE),
    // (-26, LOOP_PARAMETERS_UNAVAILABLE),
    // (-27, INVALID_RECURSION),
    // (-28, USER_INTERRUPT),
    // (-29, COMPILER_NESTING),
    // (-30, OBSOLESCENT_FEATURE),
    // (-31, GT_BODY_USED_ON_NON_CREATED_DEFINITION),
    // (-32, INVALID_NAME_ARGUMENT),
    // (-33, BLOCK_READ_EXCEPTION),
    // (-34, BLOCK_WRITE_EXCEPTION),
    // (-35, INVALID_BLOCK_NUMBER),
    // (-36, INVALID_FILE_POSITION),
    // (-37, FILE_IO_EXCEPTION),
    // (-38, NON_EXISTENT_FILE),
    // (-39, UNEXPECTED_END_OF_FILE),
    // (-40, INVALID_BASE_FOR_FLOATING_POINT_CONVERSION),
    // (-41, LOSS_OF_PRECISION),
    (-42, FLOATING_POINT_DIVIDE_BY_ZERO),
    // (-43, FLOATING_POINT_RESULT_OUT_OF_RANGE),
    (-44, FLOATING_POINT_STACK_OVERFLOW),
    (-45, FLOATING_POINT_STACK_UNDERFLOW),
    // (-46, FLOATING_POINT_INVALID_ARGUMENT),
    // (-47, COMPILATION_WORD_LIST_DELETED),
    // (-48, INVALID_POSTPONE),
    // (-49, SEARCH_ORDER_OVERFLOW),
    // (-50, SEARCH_ORDER_UNDERFLOW),
    // (-51, COMPILATION_WORD_LIST_CHANGED),
    (-52, CONTROL_FLOW_STACK_OVERFLOW),
    // (-53, EXCEPTION_STACK_OVERFLOW),
    // (-54, FLOATING_POINT_UNDERFLOW),
    // (-55, FLOATING_POINT_UNIDENTIFIED_FAULT),
    // (-56, QUIT),
    // (-57, EXCEPTION_IN_SENDING_OR_RECEIVING_A_CHARACTER),
    // (-58, SQUARE_BRACKETS_IF_ELSE_OR_THEN_EXCEPTION),
    // (-59, ALLOCATE),
    // (-60, FREE),
    // (-61, RESIZE),
    // (-62, CLOSE_FILE),
    // (-63, CREATE_FILE),
    // (-64, DELETE_FILE),
    // (-65, FILE_POSITION),
    // (-66, FILE_SIZE),
    // (-67, FILE_STATUS),
    // (-68, FLUSH_FILE),
    // (-69, OPEN_FILE),
    // (-70, READ_FILE),
    // (-71, READ_LINE),
    // (-72, RENAME_FILE),
    // (-73, REPOSITION_FILE),
    // (-74, RESIZE_FILE),
    // (-75, WRITE_FILE),
    // (-76, WRITE_LINE),
    // (-77, MALFORMED_XCHAR),
    // (-78, SUBSTITUTE),
    // (-79, REPLACES),

    // Implementation related
    (-80, INVALID_FORTH_OPERATION_KIND),
    (-81, INVALID_UNRESOLVED_FORTH_OPERATION_KIND),
    (-82, CONTROL_FLOW_STACK_UNDERFLOW),
    (-83, DO_LOOPS_STACK_UNDERFLOW),
);

struct Stack<
    'a,
    T,
    const OVERFLOW_ERROR_CODE: Cell = { Exception::STACK_OVERFLOW },
    const UNDERFLOW_ERROR_CODE: Cell = { Exception::STACK_UNDERFLOW },
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

    fn as_slice(&self) -> &[T] {
        &self.data[0..self.head]
    }

    fn backup(&self) -> Vec<T> {
        self.as_slice().to_owned()
    }

    fn restore(&mut self, backup: &[T]) {
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

/// Instructions for the interpreter
#[derive(Clone, PartialEq)]
enum ForthOperation {
    /// Push the given Cell to the data stack
    PushData(Cell),

    /// Push the next operation in the current word body into the return stack.
    /// Jump to the first instruction of the given dictionary entry.
    CallEntry(*const DictionaryEntry),

    /// Execute the given primitive function
    CallPrimitive(Primitive),

    /// Pop the return stack, jump to the popped operation.
    Next,

    /// Push the given floating number to the floating number stack
    PushFloat(Float),
}

const NAME_BYTE_COUNT: usize = 31;

#[derive(Default, PartialEq)]
struct Name {
    value: [Byte; NAME_BYTE_COUNT],
}

impl Name {
    fn from_ascii(s: &[Byte]) -> Result<Name, Exception> {
        if s.is_empty() {
            return Err(Exception::ATTEMPT_TO_USE_ZERO_LENGTH_STRING_AS_A_NAME.into());
        }

        if s.len() > NAME_BYTE_COUNT {
            return Err(Exception::DEFINITION_NAME_TOO_LONG.into());
        }

        let mut n = Name::default();
        n.value[0..s.len()].copy_from_slice(s);
        n.value.make_ascii_lowercase();

        Ok(n)
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

type Dictionary = std::collections::LinkedList<DictionaryEntry>;

#[derive(Copy, Clone, Default, Debug)]
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

    data_stack: Stack<'a, Cell, { Exception::STACK_OVERFLOW }, { Exception::STACK_UNDERFLOW }>,
    return_stack: Stack<
        'a,
        *const ForthOperation,
        { Exception::RETURN_STACK_OVERFLOW },
        { Exception::RETURN_STACK_UNDERFLOW },
    >,

    input_buffer: &'a mut [Byte],
    input_buffer_head: Cell,

    dictionary: Dictionary,

    base: Cell,

    currently_compiling: Cell,
    control_flow_stack: Stack<
        'a,
        UCell,
        { Exception::CONTROL_FLOW_STACK_OVERFLOW },
        { Exception::CONTROL_FLOW_STACK_UNDERFLOW },
    >,

    parsed_word: &'a mut [Byte],

    counted_loop_stack: Stack<
        'a,
        CountedLoopState,
        { Exception::DO_LOOPS_NESTED_TOO_DEEPLY_DURING_EXECUTION },
        { Exception::DO_LOOPS_STACK_UNDERFLOW },
    >,

    floating_point_stack: Stack<
        'a,
        Float,
        { Exception::FLOATING_POINT_STACK_OVERFLOW },
        { Exception::FLOATING_POINT_STACK_UNDERFLOW },
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

                    #[allow(unreachable_code)]
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
    ($name:literal, $method:tt, $stack: ident) => {
        declare_primitive!($name, env, {
            let b = env.$stack.pop()?;
            let a = env.$stack.pop()?;
            let c = a.$method(b);
            env.$stack.push(c)?;
        })
    };
}

macro_rules! declare_unary_operator_primitive {
    ($name:literal, $method:tt, $stack:ident) => {
        declare_primitive!($name, env, {
            let a = env.$stack.pop()?;
            let b = a.$method();
            env.$stack.push(b)?;
        })
    };
}

macro_rules! declare_compare_operator_primitive {
    ($name:literal, $operator:tt, $input_stack:ident) => {
	declare_primitive!($name, env, {
            let b = env.$input_stack.pop()?;
            let a = env.$input_stack.pop()?;
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

const STATIC_DICTIONARY: &[StaticDictionaryEntry] = &[
    declare_constant!("true", Flag::True),
    declare_constant!("false", Flag::False),
    declare_constant!("bl", b' '),
    declare_constant!("nl", b'\n'),
    declare_constant!("sizeof-cell", std::mem::size_of::<Cell>()),
    declare_constant!("sizeof-char", std::mem::size_of::<Byte>()),
    declare_constant!(
        "sizeof-forth-operation",
        std::mem::size_of::<ForthOperation>()
    ),
    declare_primitive!(".s", env, {
        let len = env.data_stack.len();
        print!("<{}> ", len);
        for i in &env.data_stack.data[0..len] {
            env.print_number(i);
        }
    }),
    declare_primitive!("bye", _env, {
        std::process::exit(0);
    }),
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
    declare_primitive!("roll", env, {
        let u = env.data_stack.pop()? as UCell;
        let amount_of_items_to_rotate = u + 1;
        let depth = env.data_stack.len();
        if depth < amount_of_items_to_rotate {
            return Err(Exception::STACK_UNDERFLOW.into());
        }

        let items_to_rotate = &mut env.data_stack.data[depth - amount_of_items_to_rotate..depth];
        items_to_rotate.rotate_left(1);
    }),
    declare_primitive!("/mod", env, {
        let divisor = env.data_stack.pop()?;
        if divisor == 0 {
            return Err(Exception::from(Exception::DIVISION_BY_ZERO));
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
    declare_binary_operator_primitive!("+", wrapping_add, data_stack),
    declare_binary_operator_primitive!("-", wrapping_sub, data_stack),
    declare_binary_operator_primitive!("*", wrapping_mul, data_stack),
    declare_binary_operator_primitive!("and", bitand, data_stack),
    declare_binary_operator_primitive!("or", bitor, data_stack),
    declare_binary_operator_primitive!("xor", bitxor, data_stack),
    declare_binary_operator_primitive!("mod", wrapping_rem, data_stack),
    declare_binary_operator_primitive!("lshift", shl, data_stack),
    declare_binary_operator_primitive!("rshift", shr, data_stack),
    declare_unary_operator_primitive!("negate", wrapping_neg, data_stack),
    declare_unary_operator_primitive!("invert", not, data_stack),
    declare_compare_operator_primitive!("=", ==, data_stack),
    declare_compare_operator_primitive!("<", <, data_stack),
    declare_compare_operator_primitive!(">", >, data_stack),
    declare_primitive!(":", env, {
        let name = env.read_name_from_input_buffer()?;
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
    declare_primitive!("'", env, {
        let name = env.read_name_from_input_buffer()?;
        let entry = search_dictionary(&env.dictionary, &name)?;
        let entry: *const DictionaryEntry = entry;
        env.data_stack.push(entry as Cell)?;
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
            ForthOperation::PushData(result) => env.data_stack.push(*result)?,
            _ => panic!("Invalid argument given to >body"),
        }
    }),
    declare_primitive!("find", env, {
        let name_address = env.data_stack.pop()?;
        let name: &CountedString =
            unsafe { (name_address as *const CountedString).as_ref() }.unwrap();
        let name = Name::from_ascii(unsafe { name.as_slice() })?;
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
        let name = env.read_name_from_input_buffer()?;
        let item = search_dictionary(&env.dictionary, &name)?;
        println!(": {} ", item.name.as_str().unwrap());
        for operation in &item.body {
            let operation_address = operation as *const ForthOperation as usize;
            print!("\t${:x}:\t", operation_address);
            match operation {
                ForthOperation::PushData(literal) => print!("PUSH-DATA\t{}", literal),
                ForthOperation::CallEntry(another_entry) => {
                    let another_entry_addr = *another_entry as usize;
                    let name = &unsafe { another_entry.as_ref() }.unwrap().name;
                    print!(
                        "CALL-ENTRY\t${:x}\t({})",
                        another_entry_addr,
                        name.as_str().unwrap()
                    )
                }
                ForthOperation::CallPrimitive(primitive) => {
                    let primitive_addr = *primitive as usize;
                    print!("CALL-PRIMITIVE\t${:x}", primitive_addr)
                }
                ForthOperation::Next => print!("NEXT"),
                ForthOperation::PushFloat(float) => print!("PUSH-FLOAT\t{}", float),
            }
            println!();
        }
        print!(";");
        if item.immediate {
            print!(" immediate");
        }
        println!()
    }),
    declare_constant!("MAX-CHAR", Byte::MAX),
    declare_constant!("ADDRESS-UNIT-BITS", Cell::BITS),
    declare_constant!("MAX-N", Cell::MAX),
    declare_constant!("MAX-U", UCell::MAX),
    declare_primitive!("MAX-D", env, {
        env.data_stack.push_double_cell(DoubleCell::MAX)?;
    }),
    declare_primitive!("MAX-UD", env, {
        env.data_stack
            .push_double_cell(DoubleUCell::MAX as DoubleCell)?;
    }),
    declare_primitive!("evaluate", env, {
        let string_byte_count = env.data_stack.pop()? as usize;
        let string_address = env.data_stack.pop()?;
        let string_address = string_address as *const u8;
        let string = unsafe { std::slice::from_raw_parts(string_address, string_byte_count) };

        // TODO: Code duplication with catch/throw?
        let input_buffer_head_backup = env.input_buffer_head;
        let input_buffer_backup = env.input_buffer.to_vec();

        // TODO: Should the return stack be saved?
        // Should this print "1 2 3" or "1 3 2" ?
        // : a s" 1 . cr 2 . cr " evaluate 3 . cr ; a

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
            return Err(Exception::DIVISION_BY_ZERO.into());
        }

        let divided: DoubleCell = env.data_stack.pop_double_cell()?;

        let divisor = divisor as DoubleCell;
        let quotient = (divided / divisor) as Cell;
        let remainder = (divided % divisor) as Cell;

        env.data_stack.push(remainder)?;
        env.data_stack.push(quotient)?;
    }),
    declare_immediate_primitive!(";", env, {
        env.latest_mut().body.push(ForthOperation::Next);
        env.currently_compiling = Flag::False as Cell;
    }),
    declare_primitive!("latest-push", env, {
        let op = env.pop_forth_operation()?;
        env.latest_mut().body.push(op);
    }),
    declare_primitive!("latest-len", env, {
        env.data_stack
            .push(env.latest().body.len() as UCell as Cell)?;
    }),
    declare_primitive!("latest!", env, {
        let index = env.data_stack.pop()? as UCell;
        let op = env.pop_forth_operation()?;
        *env.latest_mut().body.get_mut(index).unwrap() = op;
    }),
    declare_primitive!("cf>", env, {
        env.data_stack
            .push(env.control_flow_stack.pop()?.try_into().unwrap())?;
    }),
    declare_primitive!(">cf", env, {
        env.control_flow_stack
            .push(env.data_stack.pop()?.try_into().unwrap())?;
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
        let floating_point_stack_backup = env.floating_point_stack.backup();

        let err = match env.execute_word(entry.body.as_ptr()) {
            Ok(_) => 0,
            Err(exception) => {
                env.data_stack.restore(&data_stack_backup);
                env.return_stack.restore(&return_stack_backup);
                env.control_flow_stack.restore(&control_flow_stack_backup);
                env.counted_loop_stack.restore(&counted_loop_stack_backup);
                env.floating_point_stack
                    .restore(&floating_point_stack_backup);

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
    declare_primitive!("f.", env, {
        let f = env.floating_point_stack.pop()?;
        println!("{}", f);
    }),
    declare_binary_operator_primitive!("f*", mul, floating_point_stack),
    declare_binary_operator_primitive!("f+", add, floating_point_stack),
    declare_binary_operator_primitive!("f-", add, floating_point_stack),
    declare_primitive!("f/", env, {
        let divisor = env.floating_point_stack.pop()?;
        if divisor == 0.0 {
            return Err(Exception::from(Exception::FLOATING_POINT_DIVIDE_BY_ZERO));
        }

        let divided = env.floating_point_stack.pop()?;
        env.floating_point_stack.push(divided / divisor)?;
    }),
    declare_primitive!("f0=", env, {
        let f = env.floating_point_stack.pop()?;
        env.data_stack.push(Flag::from(f == 0.0) as Cell)?;
    }),
    declare_compare_operator_primitive!("f<", <, floating_point_stack),
    declare_primitive!("fdrop", env, {
        env.floating_point_stack.pop()?;
    }),
    declare_primitive!("fdup", env, {
        let f = env.floating_point_stack.pop()?;
        env.floating_point_stack.push(f)?;
        env.floating_point_stack.push(f)?;
    }),
    declare_primitive!("fover", env, {
        let a = env.floating_point_stack.pop()?;
        let b = env.floating_point_stack.pop()?;
        env.floating_point_stack.push(b)?;
        env.floating_point_stack.push(a)?;
        env.floating_point_stack.push(b)?;
    }),
    declare_primitive!("frot", env, {
        let a = env.floating_point_stack.pop()?;
        let b = env.floating_point_stack.pop()?;
        let c = env.floating_point_stack.pop()?;
        env.floating_point_stack.push(b)?;
        env.floating_point_stack.push(a)?;
        env.floating_point_stack.push(c)?;
    }),
    declare_primitive!("fswap", env, {
        let a = env.floating_point_stack.pop()?;
        let b = env.floating_point_stack.pop()?;
        env.floating_point_stack.push(a)?;
        env.floating_point_stack.push(b)?;
    }),
    declare_primitive!("fdepth", env, {
        env.data_stack
            .push(env.floating_point_stack.len() as Cell)?;
    }),
    declare_primitive!("floor", env, {
        let f = env.floating_point_stack.pop()?;
        env.floating_point_stack.push(f.floor())?;
    }),
    declare_primitive!("fround", env, {
        let f = env.floating_point_stack.pop()?;
        env.floating_point_stack.push(f.round())?;
    }),
    declare_primitive!("f@", env, {
        let address = env.data_stack.pop()? as *const Float;
        let f = unsafe { std::ptr::read_unaligned::<Float>(address) };
        env.floating_point_stack.push(f)?;
    }),
    declare_primitive!("f!", env, {
        let address = env.data_stack.pop()? as *mut Float;
        let f = env.floating_point_stack.pop()?;
        unsafe { std::ptr::write_unaligned(address, f) };
    }),
    declare_primitive!(">float", env, {
        let string_byte_count = env.data_stack.pop()? as UCell;
        let string_address = env.data_stack.pop()? as *const Byte;
        let string = unsafe { core::slice::from_raw_parts(string_address, string_byte_count) };
        match parse_float(string) {
            Some(float) => {
                env.floating_point_stack.push(float)?;
                env.data_stack.push(Flag::True as Cell)?;
            }
            _ => {
                env.data_stack.push(Flag::False as Cell)?;
            }
        }
    }),
    declare_primitive!("d>f", env, {
        let d = env.data_stack.pop_double_cell()?;
        let f = d as Float;
        env.floating_point_stack.push(f)?;
    }),
    declare_primitive!("f>d", env, {
        let f = env.floating_point_stack.pop()?;
        let d = f as DoubleCell;
        env.data_stack.push_double_cell(d)?;
    }),
    declare_primitive!("falign", env, {
        let here = unsafe { env.data_space_manager.here() } as usize;
        env.data_space_manager
            .allot(align_to_float(here) - here)
            .unwrap();
    }),
    declare_primitive!("faligned", env, {
        let address = env.data_stack.pop()? as usize;
        env.data_stack.push(align_to_float(address) as Cell)?;
    }),
    declare_unary_operator_primitive!("fabs", abs, floating_point_stack),
    declare_unary_operator_primitive!("facos", acos, floating_point_stack),
    declare_unary_operator_primitive!("facosh", acosh, floating_point_stack),
    declare_unary_operator_primitive!("falog", log10, floating_point_stack),
    declare_unary_operator_primitive!("fasin", asin, floating_point_stack),
    declare_unary_operator_primitive!("fasinh", asinh, floating_point_stack),
    declare_unary_operator_primitive!("fatan", atan, floating_point_stack),
    declare_unary_operator_primitive!("fatanh", atanh, floating_point_stack),
    declare_unary_operator_primitive!("fcos", cos, floating_point_stack),
    declare_unary_operator_primitive!("fcosh", cosh, floating_point_stack),
    declare_unary_operator_primitive!("fexp", exp, floating_point_stack),
    declare_unary_operator_primitive!("fln", ln, floating_point_stack),
    declare_unary_operator_primitive!("flog", log10, floating_point_stack),
    declare_unary_operator_primitive!("fsin", sin, floating_point_stack),
    declare_unary_operator_primitive!("fsinh", sinh, floating_point_stack),
    declare_unary_operator_primitive!("ftan", tan, floating_point_stack),
    declare_unary_operator_primitive!("ftanh", tanh, floating_point_stack),
    declare_unary_operator_primitive!("fsqrt", sqrt, floating_point_stack),
    declare_binary_operator_primitive!("f**", powf, floating_point_stack),
    declare_primitive!("fsincos", env, {
        let r1 = env.floating_point_stack.pop()?;
        let (r2, r3) = r1.sin_cos();
        env.floating_point_stack.push(r2)?;
        env.floating_point_stack.push(r3)?;
    }),
    declare_unary_operator_primitive!("fexpm1", exp_m1, floating_point_stack),
    declare_unary_operator_primitive!("flnp1", ln_1p, floating_point_stack),
    declare_binary_operator_primitive!("fatan2", atan2, floating_point_stack),
    declare_primitive!("f~", env, {
        let r3 = env.floating_point_stack.pop()?;
        let r2 = env.floating_point_stack.pop()?;
        let r1 = env.floating_point_stack.pop()?;

        let f: Flag = if r3 > 0_f32 {
            (r1 - r2) < r3
        } else if r3 == 0_f32 {
            r1 == r2
        } else {
            (r1 - r2) < (r3 * (r1.abs() + r2.abs())).abs()
        }
        .into();

        env.data_stack.push(f as Cell)?;
    }),
    declare_constant!("sizeof-float", std::mem::size_of::<Float>()),
    declare_primitive!("ms", env, {
        let ms = env.data_stack.pop()?;
        std::thread::sleep(std::time::Duration::from_millis(ms as u64));
    }),
    declare_primitive!("d+", env, {
        let d2 = env.data_stack.pop_double_cell()?;
        let d1 = env.data_stack.pop_double_cell()?;
        let d3 = d1.wrapping_add(d2);
        env.data_stack.push_double_cell(d3)?;
    }),
    declare_primitive!("d-", env, {
        let d2 = env.data_stack.pop_double_cell()?;
        let d1 = env.data_stack.pop_double_cell()?;
        let d3 = d1.wrapping_sub(d2);
        env.data_stack.push_double_cell(d3)?;
    }),
    declare_primitive!("d<", env, {
        let d2 = env.data_stack.pop_double_cell()?;
        let d1 = env.data_stack.pop_double_cell()?;
        let f: Flag = (d1 < d2).into();
        env.data_stack.push(f as Cell)?;
    }),
    declare_primitive!("dnegate", env, {
        let d1 = env.data_stack.pop_double_cell()?;
        let d2 = d1.wrapping_neg();
        env.data_stack.push_double_cell(d2)?;
    }),
    declare_primitive!("d>s", env, {
        let d = env.data_stack.pop_double_cell()?;
        let n: Cell = d
            .clamp(Cell::MIN as DoubleCell, Cell::MAX as DoubleCell)
            .try_into()
            .unwrap();
        env.data_stack.push(n)?;
    }),
    declare_primitive!("d.r", env, {
        let alignment = env.data_stack.pop()?;
        let d = env.data_stack.pop_double_cell()?;
        let string = env.format_number(d, alignment as usize);
        print!("{}", string);
    }),
    declare_primitive!("d2*", env, {
        let d = env.data_stack.pop_double_cell()?;
        env.data_stack.push_double_cell(d << 1)?;
    }),
    declare_primitive!("d2/", env, {
        let d = env.data_stack.pop_double_cell()?;
        env.data_stack.push_double_cell(d >> 1)?;
    }),
    declare_primitive!("m+", env, {
        let n = env.data_stack.pop()?;
        let d1 = env.data_stack.pop_double_cell()?;
        let d2 = d1 + n as DoubleCell;
        env.data_stack.push_double_cell(d2)?;
    }),
    declare_primitive!("m*/", env, {
        let divisor = env.data_stack.pop()?;
        if divisor == 0 {
            return Err(Exception::DIVISION_BY_ZERO.into());
        }

        if divisor < 0 {
            panic!("negative divisor");
        }

        let multiplier = env.data_stack.pop()?;
        let number = env.data_stack.pop_double_cell()?;

        // Extract sign, and treat numbers as unsigned
        let sign: DoubleCell =
            (if number < 0 { -1 } else { 1 }) * (if multiplier < 0 { -1 } else { 1 });

        let number: DoubleUCell = if number == DoubleCell::MIN {
            DoubleCell::MAX as DoubleUCell + 1
        } else {
            number.abs().try_into().unwrap()
        };

        let multiplier: UCell = DoubleCell::try_from(multiplier)
            .unwrap()
            .abs()
            .try_into()
            .unwrap();
        let divisor: UCell = divisor.try_into().unwrap();

        // Convert `number` into a three digit number. Each digit is in Cell::MAX base.
        const BASE: DoubleUCell = Cell::MAX as DoubleUCell;
        let triple_cell_number: [DoubleUCell; 3] = [
            number.div_euclid(BASE).div_euclid(BASE),
            number.div_euclid(BASE).rem_euclid(BASE),
            number.rem_euclid(BASE),
        ];
        debug_assert!(triple_cell_number[0] <= BASE);
        debug_assert!(triple_cell_number[1] <= BASE);
        debug_assert!(triple_cell_number[2] <= BASE);
        let number = triple_cell_number;

        // Multiply, by using the long multiplication algorithm
        let mut mul_result: [DoubleUCell; 3] = Default::default();
        let multiplier: DoubleUCell = multiplier.try_into().unwrap();

        mul_result[2] = number[2] * multiplier;
        mul_result[1] = mul_result[2].div_euclid(BASE);
        mul_result[2] = mul_result[2].rem_euclid(BASE);

        mul_result[1] += number[1];
        mul_result[1] *= multiplier;
        mul_result[0] = mul_result[1].div_euclid(BASE);
        mul_result[1] = mul_result[1].rem_euclid(BASE);

        mul_result[0] += number[0];
        mul_result[0] *= multiplier;

        debug_assert!(mul_result[0] <= BASE);
        debug_assert!(mul_result[1] <= BASE);
        debug_assert!(mul_result[2] <= BASE);
        let mul_result = mul_result;

        // Divide, by using the long division algorithm
        let mut divided: [DoubleUCell; 3] = mul_result;
        let divisor: DoubleUCell = divisor.try_into().unwrap();
        let mut div_result: [DoubleUCell; 3] = Default::default();

        div_result[0] = divided[0].div_euclid(divisor);
        divided[1] += divided[0].rem_euclid(divisor) * BASE;

        div_result[1] = divided[1].div_euclid(divisor);
        divided[2] += divided[1].rem_euclid(divisor) * BASE;

        div_result[2] = divided[2].div_euclid(divisor);
        debug_assert!(div_result[0] <= BASE);
        debug_assert!(div_result[1] <= BASE);
        debug_assert!(div_result[2] <= BASE);
        let div_result = div_result;

        // Lastly we convert the result back into a DoubleCell
        let unsigned_result =
            (div_result[0] * BASE * BASE) + (div_result[1] * BASE) + (div_result[2]);

        let result = if unsigned_result == (DoubleCell::MAX as DoubleUCell + 1) {
            assert_eq!(sign, -1);
            DoubleCell::MIN
        } else {
            DoubleCell::try_from(unsigned_result).unwrap() * sign
        };

        env.data_stack.push_double_cell(result)?;
    }),
];

const FORTH_RUNTIME_INIT: &str = include_str!(concat!(env!("OUT_DIR"), "/runtime.fth"));

fn search_dictionary<'a>(
    dict: &'a Dictionary,
    name: &Name,
) -> Result<&'a DictionaryEntry, Exception> {
    dict.iter()
        .find(|&item| item.name == *name)
        .ok_or(Exception::UNDEFINED_WORD.into())
}

enum ParsedNumber {
    Single(Cell),
    Double(DoubleCell),
}

fn parse_number(default_base: u32, word: &[Byte]) -> Option<ParsedNumber> {
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
    let double = *digits.last()? == b'.';
    let digits = core::str::from_utf8(if double {
        &digits[0..digits.len() - 1]
    } else {
        digits
    })
    .ok()?;

    let parsed_number: Result<ParsedNumber, std::num::ParseIntError> = if double {
        DoubleCell::from_str_radix(digits, base).map(ParsedNumber::Double)
    } else {
        Cell::from_str_radix(digits, base).map(ParsedNumber::Single)
    };

    match parsed_number {
        Err(e) => match e.kind() {
            std::num::IntErrorKind::PosOverflow | std::num::IntErrorKind::NegOverflow => {
                panic!("number too long!")
            }
            _ => None,
        },
        Ok(number) => Some(number),
    }
}

fn without_plus_at_the_start(b: &[Byte]) -> Option<&[Byte]> {
    if b.is_empty() {
        return None;
    }

    if b[0] == b'+' {
        Some(&b[1..])
    } else {
        Some(b)
    }
}

fn parse_float_significand(b: &[Byte]) -> Option<Float> {
    Float::from_str(core::str::from_utf8(without_plus_at_the_start(b)?).unwrap()).ok()
}

fn parse_float_exponent(b: &[Byte]) -> Option<i32> {
    if b.is_empty() {
        return Some(0);
    }

    match core::str::from_utf8(without_plus_at_the_start(b).unwrap())
        .unwrap()
        .parse()
    {
        Ok(e) => Some(e),
        Err(e) => match e.kind() {
            std::num::IntErrorKind::PosOverflow | std::num::IntErrorKind::NegOverflow => {
                panic!("number too long!")
            }
            std::num::IntErrorKind::Empty | std::num::IntErrorKind::Zero => Some(0),
            _ => None,
        },
    }
}

fn parse_float(word: &[Byte]) -> Option<Float> {
    let e_index = word
        .iter()
        .enumerate()
        .find(|(_, b)| [b'E', b'e'].contains(*b))
        .map(|(index, _)| index)?;

    let (before_e, e_and_after) = word.split_at(e_index);
    let after_e = &e_and_after[1..];

    let significand = parse_float_significand(before_e)?;
    let exponent = parse_float_exponent(after_e)?;

    Some(significand * 10_f32.powi(exponent))
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
        floating_point_stack_byte_count: usize,
    ) -> Option<Environment<'a>> {
        let mut data_space_manager = DataSpaceManager::new(data_space);
        let input_buffer = data_space_manager.allot(input_buffer_byte_count)?;
        let parsed_word = data_space_manager.allot(parsed_word_buffer_byte_count)?;
        let data_stack_buffer = data_space_manager.allot(data_stack_byte_count)?;
        let return_stack_buffer = data_space_manager.allot(return_stack_byte_count)?;
        let control_flow_stack_buffer = data_space_manager.allot(control_flow_stack_byte_count)?;
        let counted_loop_stack_buffer = data_space_manager.allot(counted_loop_stack_byte_count)?;
        let floating_point_stack_buffer =
            data_space_manager.allot(floating_point_stack_byte_count)?;

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
        let floating_point_stack = stack_from_byte_slice(floating_point_stack_buffer);

        let dictionary =
            std::collections::LinkedList::from_iter(STATIC_DICTIONARY.iter().map(|static_entry| {
                DictionaryEntry {
                    name: Name::from_ascii(static_entry.name.as_bytes()).unwrap(),
                    immediate: static_entry.immediate,
                    body: vec![static_entry.body.clone(), ForthOperation::Next],
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
            floating_point_stack,
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
            100 * std::mem::size_of::<Float>(),
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

        Ok(())
    }

    fn handle_token(&mut self, token: &[Byte]) -> Result<(), Exception> {
        let parse_number_result = parse_number(self.base as u32, token);

        if let Some(ParsedNumber::Single(number)) = parse_number_result {
            return self.handle_number_token(number);
        }

        if let Some(float) = parse_float(token) {
            return self.handle_float_token(float);
        }

        if let Ok(dict_entry) =
            search_dictionary(&self.dictionary, &Name::from_ascii(token).unwrap())
        {
            if self.compile_mode() && !dict_entry.immediate {
                let operation = ForthOperation::CallEntry(dict_entry);
                self.latest_mut().body.push(operation);
                return Ok(());
            }

            let next_word = &dict_entry.body;
            return self.execute_word(next_word.first().unwrap());
        }

        if let Some(ParsedNumber::Double(number)) = parse_number_result {
            let arr = double_cell_to_array(number);
            self.handle_number_token(arr[0])?;
            return self.handle_number_token(arr[1]);
        }

        Err(Exception::UNDEFINED_WORD.into())
    }

    fn handle_number_token(&mut self, data: Cell) -> Result<(), Exception> {
        if self.compile_mode() {
            let literal = ForthOperation::PushData(data);
            self.latest_mut().body.push(literal);
            Ok(())
        } else {
            self.data_stack.push(data)
        }
    }

    fn handle_float_token(&mut self, float: Float) -> Result<(), Exception> {
        if self.compile_mode() {
            let float_literal = ForthOperation::PushFloat(float);
            self.latest_mut().body.push(float_literal);
            Ok(())
        } else {
            self.floating_point_stack.push(float)
        }
    }

    fn execute_word(&mut self, entry: *const ForthOperation) -> Result<(), Exception> {
        let mut instruction_pointer = entry;
        'instruction_loop: loop {
            match unsafe { instruction_pointer.as_ref() }.unwrap() {
                ForthOperation::CallEntry(dest) => {
                    let return_address = unsafe { instruction_pointer.add(1) };
                    let dest_instruction = unsafe { dest.as_ref() }.unwrap().body.first().unwrap();
                    self.return_stack.push(return_address)?;
                    instruction_pointer = dest_instruction;
                    continue 'instruction_loop;
                }
                ForthOperation::PushData(l) => self.data_stack.push(*l)?,
                ForthOperation::CallPrimitive(func) => func(self)?,
                ForthOperation::Next => match self.return_stack.len() {
                    0 => {
                        // Nothing left to execute
                        return Ok(());
                    }
                    _ => {
                        instruction_pointer = self.return_stack.pop()?;
                        continue 'instruction_loop;
                    }
                },
                ForthOperation::PushFloat(f) => self.floating_point_stack.push(*f)?,
            }

            instruction_pointer = unsafe { instruction_pointer.add(1) };
        }
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

    fn read_name_from_input_buffer(&mut self) -> Result<Name, Exception> {
        let name = self.next_token(USUAL_LEADING_DELIMITERS_TO_IGNORE, b' ');
        Name::from_ascii(name)
    }

    fn pop_forth_operation(&mut self) -> Result<ForthOperation, Exception> {
        let kind = self.data_stack.pop()?;
        match kind {
            0 => Ok(ForthOperation::PushData(self.data_stack.pop()?)),
            1 => Ok(ForthOperation::CallEntry(
                self.data_stack.pop()? as *const DictionaryEntry
            )),
            2 => Ok(ForthOperation::CallPrimitive(unsafe {
                std::mem::transmute::<Cell, Primitive>(self.data_stack.pop()?)
            })),
            3 => Ok(ForthOperation::Next),
            4 => Ok(ForthOperation::PushFloat(self.floating_point_stack.pop()?)),
            _ => Err(Exception::INVALID_FORTH_OPERATION_KIND.into()),
        }
    }
}

/// Create a static environment
macro_rules! default_fixed_sized_environment {
    ($name:ident) => {
        let mut data_space = [0; 10 * 1024];
        let mut $name = Environment::new_default_sized(&mut data_space).unwrap();
    };
}

fn dump_stack<T, const OVERFLOW_ERROR_CODE: Cell, const UNDERFLOW_ERROR_CODE: Cell>(
    name: &str,
    s: &Stack<T, OVERFLOW_ERROR_CODE, UNDERFLOW_ERROR_CODE>,
) where
    T: Copy + std::fmt::Debug,
{
    eprintln!("\t{}: len={} items: {:?}", name, s.len(), s.as_slice());
}

fn find_dictionary_entry_from_operation(
    dict: &Dictionary,
    operation: *const ForthOperation,
) -> Option<(&str, usize)> {
    if ((operation as usize) % std::mem::align_of::<ForthOperation>()) != 0 {
        return None;
    }

    return dict.iter().find_map(|entry| {
        if entry.body.as_ptr() <= operation {
            let byte_offset = unsafe { operation.byte_offset_from(entry.body.as_ptr()) } as usize;
            let body_byte_count = entry.body.len() * std::mem::size_of::<ForthOperation>();
            if byte_offset < body_byte_count {
                let name = entry.name.as_str().ok()?;
                return Some((name, byte_offset));
            }
        }
        None
    });
}

fn dump_return_stack(
    stack: &Stack<
        *const ForthOperation,
        { Exception::RETURN_STACK_OVERFLOW },
        { Exception::RETURN_STACK_UNDERFLOW },
    >,
    dict: &Dictionary,
) {
    eprintln!("\treturn stack:");
    for (depth, operation) in stack.as_slice().iter().rev().enumerate() {
        eprint!("\t\t{}:\t${:x}", depth, *operation as usize);

        if let Some((name, offset)) = find_dictionary_entry_from_operation(dict, *operation) {
            eprint!(
                "\t({}+({} * {}))",
                name,
                offset / std::mem::size_of::<ForthOperation>(),
                std::mem::size_of::<ForthOperation>()
            );
        }

        eprintln!();
    }
}

fn main() {
    let interactive = std::io::stdin().is_terminal();
    default_fixed_sized_environment!(environment);
    for line in std::io::stdin()
        .lines()
        .map_while(|maybe_line| maybe_line.ok())
    {
        match environment.interpret_line(line.as_bytes()) {
            Ok(_) => {
                if interactive {
                    println!(" ok. ");
                }
            }
            Err(exception) => {
                eprintln!("{:?} was thrown", exception);
                eprintln!("Stack state at throw:");
                dump_stack("data", &environment.data_stack);
                dump_stack("control flow", &environment.control_flow_stack);
                dump_stack("counted loops", &environment.counted_loop_stack);
                dump_stack("floating point", &environment.floating_point_stack);
                dump_return_stack(&environment.return_stack, &environment.dictionary);

                if !interactive {
                    std::io::stdout().flush().unwrap();
                    std::io::stderr().flush().unwrap();
                    std::process::exit(1);
                }

                environment.data_stack.clear();
                environment.return_stack.clear();
                environment.control_flow_stack.clear();
                environment.counted_loop_stack.clear();
                environment.floating_point_stack.clear();
            }
        }

        std::io::stdout().flush().unwrap();
        std::io::stderr().flush().unwrap();
    }
}

#[cfg(test)]
mod tests;

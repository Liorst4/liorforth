#[cfg(test)]
mod tests {
    use crate::*;

    mod stack {
        use crate::*;

        #[test]
        fn empty() {
            let mut buffer: [Cell; 0] = Default::default();
            let mut stack = Stack::new(&mut buffer);
            assert_eq!(stack.len(), 0);
            assert_eq!(stack.push(0).err().unwrap(), StackError::Overflow);
            assert_eq!(stack.pop().err().unwrap(), StackError::Underflow);
        }

        #[test]
        fn one_item_stack() {
            let mut buffer: [Cell; 1] = Default::default();
            let mut stack = Stack::new(&mut buffer);
            assert_eq!(stack.len(), 0);
            stack.push(1).unwrap();
            assert_eq!(stack.len(), 1);
            assert_eq!(stack.push(2).err().unwrap(), StackError::Overflow);
            assert_eq!(stack.pop().unwrap(), 1);
            assert_eq!(stack.len(), 0);
        }

        #[test]
        fn sanity() {
            let mut buffer = [0, 0, 0, 0, 0];
            let mut stack = Stack::new(&mut buffer);

            stack.push(1).unwrap();
            stack.push(2).unwrap();
            stack.push(3).unwrap();
            stack.push(4).unwrap();
            stack.push(5).unwrap();
            assert_eq!(stack.len(), 5);
            assert_eq!(*stack.last().unwrap(), 5);
            assert_eq!(stack.push(5).err().unwrap(), StackError::Overflow);

            assert_eq!(stack.pop().unwrap(), 5);
            assert_eq!(stack.pop().unwrap(), 4);
            assert_eq!(stack.pop().unwrap(), 3);
            assert_eq!(stack.pop().unwrap(), 2);
            assert_eq!(stack.pop().unwrap(), 1);
            assert_eq!(stack.len(), 0);
            assert_eq!(stack.pop().err().unwrap(), StackError::Underflow);

            stack.push(1).unwrap();
            stack.push(2).unwrap();
            stack.push(3).unwrap();
            stack.push(4).unwrap();
            stack.push(5).unwrap();
            assert_eq!(stack.len(), 5);
            assert_eq!(*stack.last().unwrap(), 5);
            assert_eq!(stack.push(5).err().unwrap(), StackError::Overflow);
            stack.clear();
            assert_eq!(stack.len(), 0);
            assert_eq!(stack.pop().err().unwrap(), StackError::Underflow);
        }
    }

    #[test]
    fn initialization() {
        default_fixed_sized_environment!(_environment);
    }

    fn test_stack_effect(code: &str, env: &mut Environment, expected_result: Vec<Cell>) {
        for line in code.lines() {
            env.interpret_line(line.as_bytes());
        }
        // TODO: Print code when assert is false
        assert_eq!(
            env.data_stack.data[0..expected_result.len()],
            expected_result
        );

        assert!(env.counted_loop_stack.is_empty());
    }

    fn test_stack_effects(code_and_effects: &[(&str, Vec<Cell>)]) {
        for (code, expected_result) in code_and_effects {
            default_fixed_sized_environment!(environment);
            test_stack_effect(code, &mut environment, expected_result.clone());
        }
    }

    #[test]
    fn test_number_parsing() {
        let code_result_map: Vec<(&str, Vec<Cell>)> = vec![
            ("1234", vec![1234]),
            ("#1234", vec![1234]),
            ("$1234", vec![0x1234]),
            ("%1111", vec![0b1111]),
            ("1234 #1234 $1234 %1111", vec![1234, 1234, 0x1234, 0b1111]),
        ];
        test_stack_effects(code_result_map.as_slice());
    }

    #[test]
    fn test_division() {
        const PARAMETERS: &[(Cell, Cell, Cell, Cell)] = &[
            (1, 1, 0, 1),
            (-1, -1, 0, 1),
            (10, 5, 0, 2),
            (11, 5, 1, 2),
            (10, 7, 3, 1),
            (10, -7, 3, -1),
            (-10, 7, -3, -1),
            (-10, -7, -3, 1),
        ];

        for (a, b, expected_remainder, expected_quotient) in PARAMETERS {
            default_fixed_sized_environment!(environment);
            environment.data_stack.push(*a).unwrap();
            environment.data_stack.push(*b).unwrap();
            const SCRIPT: &str = "/mod";
            environment.interpret_line(SCRIPT.as_bytes());
            let quotient = environment.data_stack.pop().unwrap();
            let remainder = environment.data_stack.pop().unwrap();
            assert!(environment.data_stack.is_empty());
            assert_eq!((b * quotient) + remainder, *a);
            assert_eq!(quotient, *expected_quotient);
            assert_eq!(remainder, *expected_remainder);
        }
    }

    #[test]
    fn test_double_division() {
        default_fixed_sized_environment!(environment);
        const TEST_PARAMETERS: &[((DoubleCell, Cell), (Cell, Cell))] = &[
            ((10, 7), (3, 1)),
            ((-10, 7), (-3, -1)),
            ((10, -7), (3, -1)),
            ((-10, -7), (-3, 1)),
            ((Cell::MAX as DoubleCell * 2, 2), (0, Cell::MAX)),
            (((Cell::MAX as DoubleCell * 2) + 1, 2), (1, Cell::MAX)),
            ((Cell::MIN as DoubleCell * 2, 2), (0, Cell::MIN)),
            (((Cell::MIN as DoubleCell * 2) - 1, 2), (-1, Cell::MIN)),
        ];
        for ((a, b), (expected_remainder, expected_quotient)) in TEST_PARAMETERS {
            {
                environment.data_stack.push_double_cell(*a).unwrap();
                environment.data_stack.push(*b).unwrap();
                const SCRIPT: &str = "sm/rem";
                environment.interpret_line(SCRIPT.as_bytes());
                let quotient = environment.data_stack.pop().unwrap();
                let remainder = environment.data_stack.pop().unwrap();
                assert!(environment.data_stack.is_empty());

                println!("a: {} b: {}", a, b);
                println!(
                    "expected_remainder: {} remainder: {}",
                    expected_remainder, remainder
                );
                println!(
                    "expected_quotient: {} quotient: {}",
                    expected_quotient, quotient
                );

                assert_eq!(
                    *a,
                    remainder as DoubleCell + (quotient as DoubleCell * *b as DoubleCell)
                );

                assert_eq!(quotient, *expected_quotient, "quotient differ!");
                assert_eq!(remainder, *expected_remainder, "remainder differ!");
            }
        }
    }

    #[test]
    fn test_do_loop() {
        let code_result_map: Vec<(&str, Vec<Cell>)> = vec![
            (
                ": test 10 0 do 1 loop ; see test test",
                vec![1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
            ),
            (
                "
: test2
  10 0 do
       i 5 > if
             i
             unloop
             exit
       then
  loop
;
see test2
test2
",
                vec![6],
            ),
            (
                "
: test-leave
  10 0 do
       i 5 > if
             i
             .\" leavening! \" cr
             leave
       then
  loop
;
see test-leave
test-leave
",
                vec![6],
            ),
            (
                "
: test-j
  3 0 do
    5 0 do
      i j
    loop
  loop
;
see test-j
test-j
",
                vec![
                    0, 0, 1, 0, 2, 0, 3, 0, 4, 0, //
                    0, 1, 1, 1, 2, 1, 3, 1, 4, 1, //
                    0, 2, 1, 2, 2, 2, 3, 2, 4, 2, //
                ],
            ),
        ];
        test_stack_effects(code_result_map.as_slice());
    }

    #[test]
    fn return_stack_sanity() {
        default_fixed_sized_environment!(environment);

        let script = "
: a r> dup >r ;
: b a 1 ;
see a
see b
b";
        for line in script.lines() {
            environment.interpret_line(line.as_bytes());
        }

        assert_eq!(environment.data_stack.pop().unwrap(), 1);

        let something_from_return_stack = environment.data_stack.pop().unwrap();

        let b =
            search_dictionary(&environment.dictionary, &Name::from_ascii("b".as_bytes())).unwrap();

        let after_a_call = b.body.get(1).unwrap();
        match *after_a_call {
            ForthOperation::PushData(l) => {
                assert_eq!(l, 1);

                let after_a_call: *const ForthOperation = after_a_call;
                let after_a_call: Cell = after_a_call as Cell;
                assert_eq!(
                    something_from_return_stack, after_a_call,
                    "got from stack: ${:x} after_a_call: ${:x}",
                    something_from_return_stack, after_a_call
                );
            }
            _ => assert!(false),
        }
    }

    #[test]
    fn test_double_cell_encoding() {
        let numbers = [
            0,
            1,
            2,
            -1,
            -2,
            DoubleCell::MAX,
            DoubleCell::MAX / 2,
            DoubleCell::MIN,
            DoubleCell::MIN / 2,
        ];
        for number in numbers {
            assert_eq!(number, double_cell_from_array(double_cell_to_array(number)));

            let mut stack_buffer = [0; 100];
            let mut stack = Stack::new(&mut stack_buffer);
            stack.push_double_cell(number).unwrap();
            let number2 = stack.pop_double_cell().unwrap();
            assert_eq!(number, number2);
        }
    }

    #[test]
    fn test_s_to_d() {
        const INPUT_AND_EXPECTED_OUTPUT: &[(Cell, (Cell, Cell))] = &[
            (0, (0, 0)),
            (1, (1, 0)),
            (2, (2, 0)),
            (-1, (-1, -1)),
            (-2, (-2, -1)),
            (Cell::MIN, (Cell::MIN, -1)),
            (Cell::MAX, (Cell::MAX, 0)),
        ];

        default_fixed_sized_environment!(environment);

        for (input, output) in INPUT_AND_EXPECTED_OUTPUT {
            let script = format!("{} s>d", input);
            environment.interpret_line(script.as_bytes());
            let b = environment.data_stack.pop().unwrap();
            let a = environment.data_stack.pop().unwrap();
            assert!(environment.data_stack.is_empty());
            assert_eq!(*output, (a, b));
        }
    }

    #[test]
    fn test_m_star() {
        default_fixed_sized_environment!(environment);
        const TEST_PARAMETERS: &[((Cell, Cell), DoubleCell)] = &[
            ((0, 0), 0),
            ((1, 1), 1),
            (
                (Cell::MAX, Cell::MAX),
                Cell::MAX as DoubleCell * Cell::MAX as DoubleCell,
            ),
            (
                (Cell::MIN, Cell::MIN),
                Cell::MIN as DoubleCell * Cell::MIN as DoubleCell,
            ),
            ((Cell::MAX, 1), Cell::MAX as DoubleCell),
            ((Cell::MAX, 2), Cell::MAX as DoubleCell * 2 as DoubleCell),
        ];
        for ((a, b), expected_result) in TEST_PARAMETERS {
            let script = format!("{} {} m*", *a, *b);
            environment.interpret_line(script.as_bytes());
            let result: DoubleCell = environment.data_stack.pop_double_cell().unwrap();
            assert_eq!(result, *expected_result);
            assert!(environment.data_stack.is_empty());
        }
    }

    #[test]
    fn test_begin_loop() {
        let code_result_map: Vec<(&str, Vec<Cell>)> = vec![
            (
                "
: test1
  0
  begin
   1+
   dup 5 > until
;
test1
",
                vec![6],
            ),
            (
                "
: test2
  0
  begin
   1+
   dup 5 > if
    exit
   then
  true while
  repeat
;
test2
",
                vec![6],
            ),
            (
                "
: test3
  0
  begin
   1+
  dup 5 < while
   dup
  repeat
;

test3
",
                vec![1, 2, 3, 4, 5],
            ),
            (
                "
variable test4-counter
: should-continue
  test4-counter @
  1 +
  test4-counter !
  test4-counter @ 5 <
;

: test4
  begin
  0
  should-continue while
   drop
  repeat
;

test4
",
                vec![0],
            ),
        ];
        test_stack_effects(code_result_map.as_slice());
    }

    #[test]
    fn test_does() {
        let script = "
: <= ( n n -- f ) 2dup = rot rot < or ;
: array create allot does> + ;
10 array thing

0 thing
1 thing
2 thing
3 thing
";

        default_fixed_sized_environment!(environment);

        for line in script.lines() {
            environment.interpret_line(line.as_bytes());
        }

        let first = *environment.data_stack.data.get(0).unwrap();
        for i in environment.data_stack.data.iter_mut() {
            *i -= first;
        }

        assert_eq!(environment.data_stack.data[0..4], vec![0, 1, 2, 3]);
    }

    #[test]
    fn test_memory() {
        default_fixed_sized_environment!(environment);

        for number in [0, 1, -1, Cell::MAX / 2, Cell::MAX, Cell::MIN, Cell::MIN / 2] {
            {
                let mut cell_to_modify: Cell = 0;
                environment
                    .data_stack
                    .push(&mut cell_to_modify as *mut Cell as Cell)
                    .unwrap();
                environment.interpret_line(format!("{} swap !", number).as_bytes());
                assert_eq!(cell_to_modify, number);
            }

            {
                let cell_to_read: Cell = number;
                environment
                    .data_stack
                    .push(&cell_to_read as *const Cell as Cell)
                    .unwrap();
                environment.interpret_line("@".as_bytes());
                assert_eq!(cell_to_read, environment.data_stack.pop().unwrap());
            }
        }

        for number in [0, 1, 26, Byte::MAX, Byte::MAX / 2] {
            {
                let mut byte_to_modify: Byte = 0;
                environment
                    .data_stack
                    .push(&mut byte_to_modify as *mut Byte as Cell)
                    .unwrap();
                environment.interpret_line(format!("{} swap c!", number).as_bytes());
                assert_eq!(byte_to_modify, number);
            }

            {
                let byte_to_read: Byte = number;
                environment
                    .data_stack
                    .push(&byte_to_read as *const Byte as Cell)
                    .unwrap();
                environment.interpret_line("c@".as_bytes());
                assert_eq!(byte_to_read as Cell, environment.data_stack.pop().unwrap());
            }
        }
    }

    #[test]
    fn test_counted_string() {
        const STRINGS: &[&str] = &["", "a", "hello", "aaaaaaaaaa"];

        for string in STRINGS {
            let mut buffer: Vec<Byte> = vec![];
            let bytes = string.as_bytes();
            buffer.resize(bytes.len() + 1, 0);
            let counted_string = unsafe { CountedString::from_slice(bytes, &mut buffer).unwrap() };
            assert_eq!(bytes, unsafe { counted_string.as_slice() });
        }

        for string in STRINGS {
            default_fixed_sized_environment!(environment);
            environment.interpret_line(format!("bl word {}", string).as_bytes());

            let counted_string_address = *environment.data_stack.last().unwrap();
            let counted_string: &CountedString = unsafe {
                (counted_string_address as *const CountedString)
                    .as_ref()
                    .unwrap()
            };
            assert_eq!(string.as_bytes(), unsafe { counted_string.as_slice() });

            environment.interpret_line("count".as_bytes());
            let count = environment.data_stack.pop().unwrap();
            assert_eq!(count, counted_string.len as Cell);
        }
    }

    #[test]
    fn test_move() {
        default_fixed_sized_environment!(environment);
        const SRC_INITIAL_VALUE: [i32; 8] = [0, 1, 2, 3, 4, 5, 6, 7];
        let src = SRC_INITIAL_VALUE;
        let mut dest: [i32; 8] = [1; 8];

        environment.interpret_line(
            format!(
                "{} {} {} move",
                src.as_ptr() as Cell,
                dest.as_mut_ptr() as Cell,
                std::mem::size_of_val(&src),
            )
            .as_bytes(),
        );

        assert_eq!(src, SRC_INITIAL_VALUE);
        assert_eq!(dest, SRC_INITIAL_VALUE);
    }

    #[cfg(all(target_arch = "x86_64", target_os = "linux"))]
    #[test]
    fn test_syscall() {
        default_fixed_sized_environment!(environment);
        let mut forth_cwd_buffer: [Byte; 4096] = [0xff; 4096];
        let getcwd_syscall_number = 79;

        let program = format!(
            "{} {} {} 0 0 0 0 syscall drop",
            getcwd_syscall_number,
            forth_cwd_buffer.as_mut_ptr() as Cell,
            forth_cwd_buffer.len() as Cell
        );
        environment.interpret_line(program.as_bytes());

        let return_value = environment.data_stack.pop().unwrap();
        assert_ne!(return_value, -1);

        let rust_cwd = std::env::current_dir()
            .unwrap()
            .as_os_str()
            .to_str()
            .unwrap()
            .as_bytes()
            .to_owned();
        let forth_cwd_len = return_value - 1; // NULL terminator at the end
        let forth_cwd: &[u8] = &forth_cwd_buffer[0..forth_cwd_len as usize];

        assert_eq!(forth_cwd, rust_cwd);
    }
}

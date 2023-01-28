#[cfg(test)]
mod tests {
    use crate::*;

    #[test]
    fn initialization() {
        fixed_sized_buffers_environment!(_environment, 10 * 1024, 1024, 100);
    }

    fn test_stack_effect(code: &str, env: &mut Environment, expected_result: Vec<Cell>) {
        for line in code.lines() {
            env.interpret_line(line.as_bytes());
        }
        // TODO: Print code when assert is false
        assert_eq!(env.data_stack, expected_result);

        assert!(env.runtime_loops.is_empty());
    }

    fn test_stack_effects(code_and_effects: &[(&str, Vec<Cell>)]) {
        for (code, expected_result) in code_and_effects {
            fixed_sized_buffers_environment!(environment, 10 * 1024, 1024, 100);
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
        ];
        test_stack_effects(code_result_map.as_slice());
    }

    #[test]
    fn return_stack_sanity() {
        fixed_sized_buffers_environment!(environment, 10 * 1024, 1024, 100);

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

        let b = search_dictionary(&environment.dictionary, "b").unwrap();

        let after_a_call = b.body.get(1).unwrap();
        match *after_a_call {
            ForthOperation::PushCellToDataStack(l) => {
                assert_eq!(l, 1);

                let after_a_call: *const ForthOperation = after_a_call;
                let after_a_call: Cell = unsafe { std::mem::transmute(after_a_call) };
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
            0x1122334455,
        ];
        for number in numbers {
            let mut stack = Vec::new();
            push_double_cell(&mut stack, number);
            let number2 = pop_double_cell(&mut stack).unwrap();
            assert_eq!(number, number2);
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

        fixed_sized_buffers_environment!(environment, 10 * 1024, 1024, 100);

        for line in script.lines() {
            environment.interpret_line(line.as_bytes());
        }

        let first = *environment.data_stack.get(0).unwrap();
        for i in environment.data_stack.iter_mut() {
            *i -= first;
        }

        assert_eq!(environment.data_stack, vec![0, 1, 2, 3]);
    }
}

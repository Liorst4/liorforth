#[cfg(test)]
mod tests {
    use crate::*;

    #[test]
    fn initialization() {
        let mut data_space = [0; 10 * 1024];
        let mut input_buffer = [0; 1024];
        let mut _environment = Environment::new(&mut data_space, &mut input_buffer);
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
            let mut data_space = [0; 10 * 1024];
            let mut input_buffer = [0; 1024];
            let mut environment = Environment::new(&mut data_space, &mut input_buffer);
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
    fn test_loop() {
        let code_result_map: Vec<(&str, Vec<Cell>)> = vec![(
            ": test 10 0 do 1 loop ; see test test",
            vec![1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
        )];
        test_stack_effects(code_result_map.as_slice());
    }

    #[test]
    fn return_stack_sanity() {
        let mut data_space = [0; 10 * 1024];
        let mut input_buffer = [0; 1024];
        let mut environment = Environment::new(&mut data_space, &mut input_buffer);

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
        let b = unsafe { b.as_ref() }.unwrap();

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
}

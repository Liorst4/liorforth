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
            env.interpret_line(line);
        }
        // TODO: Print code when assert is false
        assert_eq!(env.data_stack, expected_result);
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
}

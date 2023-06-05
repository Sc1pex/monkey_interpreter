use super::*;

mod expressions;
mod statements;

type TestResult = std::result::Result<(), Vec<String>>;

fn assert_expected(expected: Block, program: Block) {
    assert_eq!(expected.statements.len(), program.statements.len());
    for (e, s) in expected.statements.iter().zip(program.statements.iter()) {
        assert_eq!(e, s);
    }
}

fn test(input: &str, expected: Block) -> TestResult {
    let mut parser = Parser::new(Lexer::new(input));
    let program = parser.parse()?;
    assert_expected(expected, program);
    Ok(())
}

#[test]
fn opearator_precedence() -> TestResult {
    let tests = vec![
        ("-a * b", "((-a) * b)\n"),
        ("!-a", "(!(-a))\n"),
        ("a + b + c", "((a + b) + c)\n"),
        ("a + b - c", "((a + b) - c)\n"),
        ("a * b * c", "((a * b) * c)\n"),
        ("a * b / c", "((a * b) / c)\n"),
        ("a + b / c", "(a + (b / c))\n"),
        ("a + b * c + d / e - f", "(((a + (b * c)) + (d / e)) - f)\n"),
        ("3 + 4; -5 * 5", "(3 + 4)\n((-5) * 5)\n"),
        ("5 > 4 == 3 < 4", "((5 > 4) == (3 < 4))\n"),
        ("5 < 4 != 3 > 4", "((5 < 4) != (3 > 4))\n"),
        (
            "3 + 4 * 5 == 3 * 1 + 4 * 5",
            "((3 + (4 * 5)) == ((3 * 1) + (4 * 5)))\n",
        ),
        ("1 + (2 + 3) + 4", "((1 + (2 + 3)) + 4)\n"),
        (
            "add(a, b, 1, 2 * 3, 4 + 5, add(6, 7 * 8))",
            "add(a, b, 1, (2 * 3), (4 + 5), add(6, (7 * 8)))\n",
        ),
        (
            "a * [1, 2, 3, 4][b * c] * d",
            "((a * ([1, 2, 3, 4][(b * c)])) * d)\n",
        ),
        (
            "add(a * b[2], b[1], 2 * [1, 2][1])",
            "add((a * (b[2])), (b[1]), (2 * ([1, 2][1])))\n",
        ),
    ];

    for t in tests {
        let mut parser = Parser::new(Lexer::new(t.0));
        let r = parser.parse()?.to_string();
        assert_eq!(r, t.1);
    }

    Ok(())
}

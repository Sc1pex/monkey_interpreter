use super::*;

mod expressions;
mod statements;

fn check_errors(p: &Parser) {
    assert_eq!(
        p.errors.len(),
        0,
        "Parser had {} errors:\n{:?}",
        p.errors.len(),
        p.errors
    );
}

#[test]
fn opearator_precedence() {
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
    ];

    for t in tests {
        let mut parser = Parser::new(Lexer::new(t.0));
        let r = parser.parse().to_string();
        check_errors(&parser);
        assert_eq!(r, t.1);
    }
}

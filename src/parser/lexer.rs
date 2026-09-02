//! A lexer for the SMT-LIB and Alethe formats.

use crate::{
    CarcaraResult, Error,
    ast::impl_str_conversion_traits,
    parser::{ParserError, Source},
};
use rug::{Integer, Rational, ops::Pow};
use std::{
    path::Path,
    str::FromStr,
};

/// A token in the SMT-LIB and Alethe formats.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Token {
    /// The `(` token.
    OpenParen,

    /// The `)` token.
    CloseParen,

    /// A symbol, that can be either simple or quoted.
    ///
    /// A simple symbol is a non-empty sequence of letters, digits, or any of these characters: `+`,
    /// `-`, `/`, `*`, `=`, `%`, `?`, `!`, `.`, `$`, `_`, `~`, `&`, `^`, `<`, `>`, or `@`. A quoted
    /// symbol is any sequence of characters that starts and ends with `|`, and does not contain `|`
    /// or `\`.
    Symbol(String),

    /// A keyword, which is a simple symbol preceded by `:`. This has the leading `:` character
    /// removed.
    Keyword(String),

    /// An integer numeral literal.
    Numeral(Integer),

    /// A decimal numeral literal.
    Decimal(Rational),

    /// A bitvector literal, represented by its integer value and width.
    Bitvector(Integer, usize),

    /// A string literal.
    String(String),

    /// A reserved word.
    ReservedWord(Reserved),

    /// A signal token to indicate the end of the input.
    Eof,
}

/// A reserved word in the SMT-LIB and Alethe lexicon.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Reserved {
    /// The `_` reserved word.
    Underscore,

    /// The `!` reserved word.
    Bang,

    /// The `as` reserved word.
    As,

    /// The `let` reserved word.
    Let,

    /// The `exists` reserved word.
    Exists,

    /// The `forall` reserved word.
    Forall,

    /// The `match` reserved word.
    Match,

    /// The `choice` reserved word.
    Choice,

    /// The `lambda` reserved word.
    Lambda,

    /// The `cl` reserved word.
    Cl,

    /// The `assume` reserved word.
    Assume,

    /// The `step` reserved word.
    Step,

    /// The `anchor` reserved word.
    Anchor,

    /// The `declare-fun` reserved word.
    DeclareFun,

    /// The `declare-const` reserved word.
    DeclareConst,

    /// The `declare-sort` reserved word.
    DeclareSort,

    /// The `declare-datatype` reserved word.
    DeclareDatatype,

    /// The `declare-datatypes` reserved word.
    DeclareDatatypes,

    /// The `par` reserved word.
    Par,

    /// The `define-fun` reserved word.
    DefineFun,

    /// The `define-fun-rec` reserved word.
    DefineFunRec,

    /// The `define-funs-rec` reserved word.
    DefineFunsRec,

    /// The `define-sort` reserved word.
    DefineSort,

    /// The `assert` reserved word.
    Assert,

    /// The `check-sat-assuming` reserved word.
    CheckSatAssuming,

    /// The `set-logic` reserved word.
    SetLogic,

    /// The `declare-rare-rule` reserved word.
    DeclareRareRule,
}

impl_str_conversion_traits!(Reserved {
    Underscore: "_",
    Bang: "!",
    As: "as",
    Let: "let",
    Exists: "exists",
    Forall: "forall",
    Match: "match",
    Choice: "choice",
    Lambda: "lambda",
    Cl: "cl",
    Assume: "assume",
    Step: "step",
    Anchor: "anchor",
    DeclareFun: "declare-fun",
    DeclareDatatype: "declare-datatype",
    DeclareDatatypes: "declare-datatypes",
    Par: "par",
    DeclareConst: "declare-const",
    DeclareSort: "declare-sort",
    DefineFun: "define-fun",
    DefineFunRec: "define-fun-rec",
    DefineFunsRec: "define-funs-rec",
    DefineSort: "define-sort",
    Assert: "assert",
    CheckSatAssuming: "check-sat-assuming",
    SetLogic: "set-logic",
    DeclareRareRule: "declare-rare-rule"
});

/// Represents a position (line and column numbers) in the source input.
pub type Position = (usize, usize);

/// A lexer for the SMT-LIB, Alethe and Rare lexicons.
///
/// The lexer is a cursor over the raw bytes of the source. Tokens are scanned byte-wise (an
/// ASCII-delimited grammar makes this safe even for UTF-8 input: continuation bytes never match
/// an ASCII delimiter) and their text is taken as a slice of the source, so producing a token
/// costs at most one exact-size allocation. Byte classification goes through a lookup table
/// instead of character predicate chains, and no byte is ever decoded twice.
pub struct Lexer<'s> {
    src: &'s str,
    bytes: &'s [u8],
    pos: usize,
    line_start: usize,
    lines_read: usize,
    pub source_name: &'s Path,
}

/// Lookup table for the bytes that can appear in a simple symbol: ASCII alphanumerics, the symbol
/// punctuation of the SMT-LIB and Alethe formats, and `'`, which Carcara uses for variables
/// renamed by capture-avoidance (see `utils::is_symbol_character`).
static SYMBOL_BYTE: [bool; 256] = {
    let mut table = [false; 256];
    let mut b = 0usize;
    while b < 256 {
        let c = b as u8;
        table[b] = c.is_ascii_alphanumeric()
            || matches!(
                c,
                b'+' | b'-'
                    | b'/'
                    | b'*'
                    | b'='
                    | b'%'
                    | b'?'
                    | b'!'
                    | b'.'
                    | b'$'
                    | b'_'
                    | b'~'
                    | b'&'
                    | b'^'
                    | b'<'
                    | b'>'
                    | b'@'
                    | b'\''
            );
        b += 1;
    }
    table
};

impl<'s> Lexer<'s> {
    /// Constructs a new `Lexer` from a `Source`.
    pub fn new(source: Source<'s>) -> Self {
        Self {
            src: source.contents,
            bytes: source.contents.as_bytes(),
            pos: 0,
            line_start: 0,
            lines_read: 0,
            source_name: source.name,
        }
    }

    /// Wraps a `ParserError` into a crate level error, by adding the current position and the
    /// current source name.
    fn err(&self, inner: impl Into<ParserError>) -> Error {
        Error::Parser(inner.into(), self.position(), self.source_name.into())
    }

    /// Returns the byte at the cursor, without advancing.
    #[inline]
    fn peek(&self) -> Option<u8> {
        self.bytes.get(self.pos).copied()
    }

    /// Advances the cursor by one byte, keeping the line bookkeeping. Continuation bytes of a
    /// multi-byte character never equal `\n`, so advancing through one byte at a time is safe.
    #[inline]
    fn bump(&mut self) {
        if self.bytes[self.pos] == b'\n' {
            self.lines_read += 1;
            self.line_start = self.pos + 1;
        }
        self.pos += 1;
    }

    /// Decodes the character at the cursor. Only used on the cold paths (errors, string literal
    /// contents, and non-ASCII input).
    fn current_char(&self) -> Option<char> {
        self.src[self.pos..].chars().next()
    }

    /// Advances the cursor past the character at it (of any byte length).
    fn bump_char(&mut self) {
        if let Some(c) = self.current_char() {
            for _ in 0..c.len_utf8() {
                self.bump();
            }
        }
    }

    /// Advances the lexer by one line, discarding the remaining contents of the current line.
    fn next_line(&mut self) {
        while let Some(b) = self.peek() {
            let was_newline = b == b'\n';
            self.bump();
            if was_newline {
                break;
            }
        }
    }

    /// Returns the position of the current character.
    fn position(&self) -> Position {
        // + 1 because lines and columns are usually counted starting from 1
        (self.lines_read + 1, self.pos - self.line_start + 1)
    }

    /// Scans bytes while they satisfy `predicate`, and returns them as a slice of the source. The
    /// predicate must only accept ASCII bytes, so the slice always ends on a character boundary.
    #[inline]
    fn scan_while<P: Fn(u8) -> bool>(&mut self, predicate: P) -> &'s str {
        let start = self.pos;
        while let Some(b) = self.peek() {
            if !predicate(b) {
                break;
            }
            self.bump();
        }
        &self.src[start..self.pos]
    }

    /// Consumes all leading whitespace and comments in the input source.
    fn consume_whitespace(&mut self) {
        loop {
            match self.peek() {
                Some(b' ' | b'\t' | b'\n' | b'\r' | 0x0b | 0x0c) => self.bump(),
                Some(b';') => self.next_line(),
                // Non-ASCII whitespace is accepted for compatibility with the previous
                // character-based lexer, though it does not occur in practice
                Some(b) if b >= 0x80 && self.current_char().is_some_and(char::is_whitespace) => {
                    self.bump_char();
                }
                _ => break,
            }
        }
    }

    /// Reads a token from the input source.
    pub fn next_token(&mut self) -> CarcaraResult<(Token, Position)> {
        self.consume_whitespace();
        let start_position = self.position();
        let token = match self.peek() {
            Some(b'(') => {
                self.bump();
                Ok(Token::OpenParen)
            }
            Some(b')') => {
                self.bump();
                Ok(Token::CloseParen)
            }
            Some(b'"') => self.read_string(),
            Some(b'|') => self.read_quoted_symbol(),
            Some(b':') => Ok(self.read_keyword()),
            Some(b'#') => self.read_bitvector(),
            Some(b'-') => {
                // If we encounter the '-' character, the token can either be a GMP-style numerical
                // literal (e.g. '-5'), or a symbol that starts with '-' (e.g. the '-' operator
                // itself)
                if self.bytes.get(self.pos + 1).is_some_and(u8::is_ascii_digit) {
                    self.bump();
                    self.read_number(true)
                } else {
                    // This assumes that the symbol is never a reserved word. Since '-' is itself a
                    // symbol byte, scanning from here includes it in the token
                    let symbol = self.scan_while(|b| SYMBOL_BYTE[b as usize]);
                    Ok(Token::Symbol(symbol.to_owned()))
                }
            }
            Some(b) if b.is_ascii_digit() => self.read_number(false),
            Some(b) if SYMBOL_BYTE[b as usize] => Ok(self.read_simple_symbol()),
            None => Ok(Token::Eof),
            Some(_) => Err(self.err(ParserError::UnexpectedChar(
                self.current_char().unwrap(),
            ))),
        }?;
        Ok((token, start_position))
    }

    /// Reads a simple symbol from the input source.
    fn read_simple_symbol(&mut self) -> Token {
        let symbol = self.scan_while(|b| SYMBOL_BYTE[b as usize]);
        if let Ok(reserved) = Reserved::from_str(symbol) {
            Token::ReservedWord(reserved)
        } else {
            Token::Symbol(symbol.to_owned())
        }
    }

    /// Reads a quoted symbol from the input source.
    fn read_quoted_symbol(&mut self) -> CarcaraResult<Token> {
        self.bump(); // Consume `|`
        let start = self.pos;
        while let Some(b) = self.peek() {
            if b == b'|' || b == b'\\' {
                break;
            }
            self.bump();
        }
        match self.peek() {
            Some(b'\\') => Err(self.err(ParserError::BackslashInQuotedSymbol)),
            None => Err(self.err(ParserError::EofInQuotedSymbol)),
            Some(_) => {
                let symbol = self.src[start..self.pos].to_owned();
                self.bump();
                Ok(Token::Symbol(symbol))
            }
        }
    }

    /// Reads a keyword from the input source.
    fn read_keyword(&mut self) -> Token {
        self.bump(); // Consume `:`
        let symbol = self.scan_while(|b| SYMBOL_BYTE[b as usize]);
        Token::Keyword(symbol.to_owned())
    }

    /// Reads a binary or hexadecimal bitvector literal, e.g. `#b0110` or `#x01Ab`.
    ///
    /// Returns an error if any character other than `b` or `x` is encountered after the `#`, or if
    /// no digits are provided.
    fn read_bitvector(&mut self) -> CarcaraResult<Token> {
        self.bump(); // Consume `#`
        let (base, bits_per_char) = match self.peek() {
            Some(b'b') => (2, 1),
            Some(b'x') => (16, 4),
            None => return Err(self.err(ParserError::EmptyBitvector)),
            Some(_) => {
                return Err(self.err(ParserError::UnexpectedChar(
                    self.current_char().unwrap(),
                )));
            }
        };
        self.bump();
        let s = self.scan_while(|b| (b as char).is_digit(base as u32));
        if s.is_empty() {
            return Err(self.err(ParserError::EmptyBitvector));
        }

        let width = s.len() * bits_per_char;
        let value = Integer::from_str_radix(s, base).unwrap();
        Ok(Token::Bitvector(value, width))
    }

    /// Reads an integer or decimal numerical literal.
    fn read_number(&mut self, negated: bool) -> CarcaraResult<Token> {
        let first_part = self.scan_while(|b| b.is_ascii_digit());

        if first_part.len() > 1 && first_part.starts_with('0') {
            return Err(self.err(ParserError::LeadingZero(first_part.to_owned())));
        }

        if let Some(delimiter @ (b'/' | b'.')) = self.peek() {
            self.bump();
            let second_part = self.scan_while(|b| b.is_ascii_digit());
            if let Some(b'/' | b'.') = self.peek() {
                // A number can have only one delimiter
                let e = ParserError::UnexpectedChar(self.current_char().unwrap());
                return Err(self.err(e));
            }
            let r = match delimiter {
                b'/' => {
                    let [numer, denom] =
                        [first_part, second_part].map(|s| s.parse::<Integer>().unwrap());
                    if denom.is_zero() {
                        let e = ParserError::DivisionByZeroInLiteral(format!("{numer}/{denom}"));
                        return Err(self.err(e));
                    }
                    Rational::from((numer, denom))
                }
                b'.' => {
                    let denom = Integer::from(10u32).pow(second_part.len() as u32);
                    let numer = [first_part, second_part]
                        .concat()
                        .parse::<Integer>()
                        .unwrap();
                    Rational::from((numer, denom))
                }
                _ => unreachable!(),
            };
            Ok(Token::Decimal(if negated { -r } else { r }))
        } else {
            let i: Integer = first_part.parse().unwrap();
            Ok(Token::Numeral(if negated { -i } else { i }))
        }
    }

    /// Reads a string literal from the input source.
    fn read_string(&mut self) -> CarcaraResult<Token> {
        self.bump(); // Consume `"`
        let mut result = String::new();
        loop {
            // Copy plain content in runs: scan up to the next delimiter and append the whole
            // slice at once (multi-byte characters pass through untouched)
            let start = self.pos;
            while let Some(b) = self.peek() {
                if b == b'"' || b == b'\\' {
                    break;
                }
                self.bump();
            }
            result.push_str(&self.src[start..self.pos]);
            match self.peek() {
                None => return Err(self.err(ParserError::EofInString)),
                Some(b'"') => {
                    self.bump();
                    if self.peek() == Some(b'"') {
                        result.push('"');
                        self.bump();
                    } else {
                        break;
                    }
                }
                Some(_) => {
                    // A backslash: either a unicode escape sequence, or a literal backslash
                    self.bump();
                    if self.peek() == Some(b'u') {
                        self.bump();
                        self.read_unicode_escape_sequence(&mut result)?;
                    } else {
                        result.push('\\');
                    }
                }
            }
        }
        Ok(Token::String(result))
    }

    /// Reads a unicode escape sequence encountered in a string literal, denoted by `\uXXXX` or
    /// `\u{...}`.
    fn read_unicode_escape_sequence(&mut self, result: &mut String) -> CarcaraResult<()> {
        // At this point, '\' and 'u' have already been read
        match self.peek() {
            Some(b'{') => {
                self.bump();
                // Read the contents inside the {} braces, up to five hex characters
                let start = self.pos;
                for _ in 0..5 {
                    match self.peek() {
                        None => return Err(self.err(ParserError::EofInString)),
                        Some(b) if b == b'}' || !b.is_ascii_hexdigit() => break,
                        Some(_) => self.bump(),
                    }
                }
                let contents = &self.src[start..self.pos];
                if self.peek() == Some(b'}') {
                    self.bump();
                } else {
                    // If the contents are not up to 5 hex digits followed by '}', this is not a
                    // well-formed unicode escape sequence, so we abort
                    result.push_str("\\u{");
                    result.push_str(contents);
                    return Ok(());
                }
                if contents.is_empty() {
                    // Handle "\u{}" edge case
                    result.push_str("\\u{}");
                    return Ok(());
                }
                let code = u32::from_str_radix(contents, 16).unwrap();

                // In the SMT-LIB unicode escape syntax, only the planes 0 to 2 of Unicode are
                // allowed, meaning values up to 0x2FFFF. For values beyond that, we treat the
                // escape sequence as a literal string.
                if code > 0x2FFFF {
                    result.push_str("\\u{");
                    result.push_str(contents);
                    result.push('}');
                    return Ok(());
                }

                // While the previous check ensures that the codepoint is not out-of-bounds for
                // Unicode, it might still lie in the Unicode High Surrogate Area (0xD800 to
                // 0xDFFF), which is also considered invalid. Therefore `char::from_u32` may still
                // fail.
                let c = char::from_u32(code)
                    .ok_or_else(|| self.err(ParserError::InvalidUnicode(contents.to_owned())))?;
                result.push(c);
                Ok(())
            }
            Some(_) => {
                let start = self.pos;
                for _ in 0..4 {
                    match self.peek() {
                        None => return Err(self.err(ParserError::EofInString)),
                        Some(b) if !b.is_ascii_hexdigit() => break,
                        Some(_) => self.bump(),
                    }
                }
                let contents = &self.src[start..self.pos];
                if contents.len() != 4 {
                    // If the contents are not exactly 4 hex digits, this is not a well-formed
                    // unicode escape sequence, so we abort
                    result.push_str("\\u");
                    result.push_str(contents);
                    return Ok(());
                }
                let code = u32::from_str_radix(contents, 16).unwrap();
                let c = char::from_u32(code)
                    .ok_or_else(|| self.err(ParserError::InvalidUnicode(contents.to_owned())))?;
                result.push(c);
                Ok(())
            }
            None => Err(self.err(ParserError::EofInString)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lex_one(input: &str) -> CarcaraResult<Token> {
        Lexer::new(input.into()).next_token().map(|(tk, _)| tk)
    }

    fn lex_all(input: &str) -> Vec<Token> {
        let mut lex = Lexer::new(input.into());
        let mut result = Vec::new();
        loop {
            let tk = lex.next_token().expect("lexer error during test").0;
            if tk == Token::Eof {
                break;
            }
            result.push(tk);
        }
        result
    }

    #[test]
    fn test_empty_input() {
        assert_eq!(lex_all(""), vec![]);
        assert_eq!(lex_all("   \n  \n\n "), vec![]);
        assert_eq!(lex_all("; comment\n"), vec![]);
    }

    #[test]
    fn test_comments() {
        assert_eq!(
            lex_all("; comment\n symbol\n ; comment"),
            vec![Token::Symbol("symbol".into())]
        );
        assert_eq!(
            lex_all(";\n;\nsymbol ;\n symbol"),
            vec![
                Token::Symbol("symbol".into()),
                Token::Symbol("symbol".into())
            ]
        );
    }

    #[test]
    fn test_simple_symbols_and_keywords() {
        let input = "foo123 :foo123 :a:b +-/*=%?!.$_~&^<>@ -starts-with-dash --double-dash";
        let expected = vec![
            Token::Symbol("foo123".into()),
            Token::Keyword("foo123".into()),
            Token::Keyword("a".into()),
            Token::Keyword("b".into()),
            Token::Symbol("+-/*=%?!.$_~&^<>@".into()),
            Token::Symbol("-starts-with-dash".into()),
            Token::Symbol("--double-dash".into()),
        ];
        assert_eq!(expected, lex_all(input));
    }

    #[test]
    fn test_quoted_symbols() {
        let input = "|abc| abc |:abc| || |\n\t |";
        let expected = vec![
            Token::Symbol("abc".into()),
            Token::Symbol("abc".into()),
            Token::Symbol(":abc".into()),
            Token::Symbol("".into()),
            Token::Symbol("\n\t ".into()),
        ];
        assert_eq!(expected, lex_all(input));

        assert!(matches!(
            lex_one("|\\|"),
            Err(Error::Parser(ParserError::BackslashInQuotedSymbol, _, _))
        ));

        assert!(matches!(
            lex_one("|"),
            Err(Error::Parser(ParserError::EofInQuotedSymbol, _, _))
        ));
    }

    #[test]
    fn test_numerals_and_decimals() {
        let input = "42 3.14159 -137 8/3 -5/2 1/1 0/2";
        let expected = vec![
            Token::Numeral(42.into()),
            Token::Decimal((314_159, 100_000).into()),
            Token::Numeral((-137).into()),
            Token::Decimal((8, 3).into()),
            Token::Decimal((-5, 2).into()),
            Token::Decimal(1.into()),
            Token::Decimal(0.into()),
        ];
        assert_eq!(expected, lex_all(input));

        assert!(matches!(
            lex_one("0123"),
            Err(Error::Parser(ParserError::LeadingZero(_), _, _))
        ));
        assert!(matches!(
            lex_one("1.2.3"),
            Err(Error::Parser(ParserError::UnexpectedChar(_), _, _))
        ));
        assert!(matches!(
            lex_one("1/2.3"),
            Err(Error::Parser(ParserError::UnexpectedChar(_), _, _))
        ));
        assert!(matches!(
            lex_one("1.2/3"),
            Err(Error::Parser(ParserError::UnexpectedChar(_), _, _))
        ));
        assert!(matches!(
            lex_one("1/0"),
            Err(Error::Parser(ParserError::DivisionByZeroInLiteral(_), _, _))
        ));
    }

    #[test]
    fn test_bitvectors() {
        let input = "#b101010 #xdeadbeef #b1 #x0";
        let expected = vec![
            Token::Bitvector(42.into(), 6),
            Token::Bitvector(0xdeadbeefu64.into(), 32),
            Token::Bitvector(1.into(), 1),
            Token::Bitvector(0.into(), 4),
        ];
        assert_eq!(expected, lex_all(input));

        assert!(matches!(
            lex_one("#o123"),
            Err(Error::Parser(ParserError::UnexpectedChar('o'), _, _)),
        ));

        assert!(matches!(
            lex_one("#"),
            Err(Error::Parser(ParserError::EmptyBitvector, _, _)),
        ));

        assert!(matches!(
            lex_one("#b"),
            Err(Error::Parser(ParserError::EmptyBitvector, _, _)),
        ));
    }

    #[test]
    fn test_strings() {
        let input = r#" "string" "escaped quote: """ """" """""" "\u0061" "\u{0061}" "#;
        let expected = vec![
            Token::String("string".into()),
            Token::String("escaped quote: \"".into()),
            Token::String("\"".into()),
            Token::String("\"\"".into()),
            Token::String("a".into()),
            Token::String("a".into()),
        ];
        assert_eq!(expected, lex_all(input));

        assert!(matches!(
            lex_one("\""),
            Err(Error::Parser(ParserError::EofInString, _, _))
        ));
        assert!(matches!(
            lex_one("\"\\u{de01}\""),
            Err(Error::Parser(ParserError::InvalidUnicode(_), _, _))
        ));
    }

    #[test]
    fn test_weird_unicode_escape_sequences() {
        let input = r#"
            "\u{61}" "\u{00061}" "\u{000061}" "\u00061" "\u61"
            "\u" "\u{12x4}" "\u{123" "\u{}" "\u{30000}" "#;
        let expected = [
            "a",
            "a",
            "\\u{000061}",
            "\u{0006}1",
            "\\u61",
            "\\u",
            "\\u{12x4}",
            "\\u{123",
            "\\u{}",
            "\\u{30000}",
        ]
        .map(str::to_owned)
        .map(Token::String);
        assert_eq!(expected.as_slice(), lex_all(input));
    }

    #[test]
    fn test_reserved_words() {
        let input = "_ ! as let exists |_| |!| |as| |let| |exists|";
        let expected = vec![
            Token::ReservedWord(Reserved::Underscore),
            Token::ReservedWord(Reserved::Bang),
            Token::ReservedWord(Reserved::As),
            Token::ReservedWord(Reserved::Let),
            Token::ReservedWord(Reserved::Exists),
            Token::Symbol("_".into()),
            Token::Symbol("!".into()),
            Token::Symbol("as".into()),
            Token::Symbol("let".into()),
            Token::Symbol("exists".into()),
        ];
        assert_eq!(expected, lex_all(input));
    }
}

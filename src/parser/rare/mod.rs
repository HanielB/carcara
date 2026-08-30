use super::{Parser, ParserError, Reserved, SortDef, Token};
use crate::ast::*;
use crate::CarcaraResult;
use crate::ast::rare_rules::*;

#[derive(Debug, Clone)]
enum Body {
    Conclusion(Rc<Term>),
    Premise(Vec<Rc<Term>>),
    Args(Vec<String>),
}

struct BodyDefinition<'a> {
    args: &'a Vec<String>,
    premises: &'a Vec<Rc<Term>>,
    conclusion: Option<Rc<Term>>,
}

impl<'p, 's> Parser<'p, 's> {
    fn parse_rare_parameters(&mut self) -> CarcaraResult<(String, TypeParameter)> {
        self.expect_token(Token::OpenParen)?;
        let name = self.expect_symbol()?;
        let sort = self.parse_sort()?;

        let attribute = match self.current_token.clone() {
            Token::CloseParen => {
                self.expect_token(Token::CloseParen)?;
                AttributeParameters::None
            }
            Token::Keyword(_) => {
                let kind_of_arg = self.expect_keyword()?;
                self.expect_token(Token::CloseParen)?;
                if kind_of_arg == "list" {
                    AttributeParameters::List
                } else {
                    return Err(self.err(
                        ParserError::InvalidRareArgAttribute(kind_of_arg),
                        self.current_position,
                    ));
                }
            }
            token => {
                return Err(self.err(ParserError::UnexpectedToken(token), self.current_position));
            }
        };

        // With sorts separated from terms there is no `(rare-list S)` sort: a `:list` parameter's
        // variable is typed at the element sort directly
        self.declare_symbol(name.clone(), sort.clone());
        let variable = self.pool.add(Term::new_var(name.clone(), sort.clone()));
        self.state.sort_defs.insert(
            name.clone(),
            SortDef {
                body: sort.clone(),
                params: Vec::default(),
            },
        );

        // Accept both `T` and `@T` references for rare type parameters declared as `Type`.
        // This keeps compatibility with rule files that declare `(T0 Type)` but use `@T0`.
        if matches!(sort.as_ref(), Sort::Type) {
            let alias = if let Some(stripped) = name.strip_prefix('@') {
                stripped.to_owned()
            } else {
                format!("@{}", name)
            };

            let type_sort = self.pool.add_sort(Sort::Type);
            self.state
                .sort_defs
                .entry(alias)
                .or_insert_with(|| SortDef {
                    body: type_sort,
                    params: Vec::default(),
                });
        }

        Ok((name, TypeParameter { sort, attribute, variable }))
    }

    fn parse_body(&mut self) -> CarcaraResult<Body> {
        let qualified_arg = self.expect_keyword()?;
        match qualified_arg.as_str() {
            "conclusion" => {
                let rewrite_term = self.parse_term()?;
                Ok(Body::Conclusion(rewrite_term))
            }
            "args" => {
                self.expect_token(Token::OpenParen)?;
                let args = self.parse_sequence(Parser::expect_symbol, false)?;
                Ok(Body::Args(args))
            }
            "premises" => {
                self.expect_token(Token::OpenParen)?;
                let terms = self.parse_sequence(
                    |parser| {
                        let term = parser.parse_term()?;
                        Ok(term)
                    },
                    false,
                )?;
                Ok(Body::Premise(terms))
            }
            _ => Err(self.err(
                ParserError::InvalidRareRuleAttribute(qualified_arg),
                self.current_position,
            )),
        }
    }

    fn parse_rule(&mut self) -> CarcaraResult<RuleDefinition> {
        self.expect_token(Token::OpenParen)?;
        self.expect_token(Token::ReservedWord(Reserved::DeclareRareRule))?;
        let name = self.expect_symbol()?;
        self.expect_token(Token::OpenParen)?;
        let parameters = self.parse_sequence(Self::parse_rare_parameters, false)?;

        let body_definitions = BodyDefinition {
            args: &vec![],
            premises: &vec![],
            conclusion: None,
        };

        let body = self.parse_sequence(Self::parse_body, false)?;
        let body = body.iter().fold(body_definitions, |mut body, x| {
            match x {
                Body::Conclusion(term) => body.conclusion = Some((*term).clone()),
                Body::Premise(term) => body.premises = term,
                Body::Args(args) => body.args = args,
            }
            body
        });

        if body.conclusion.is_none() {
            return Err(self.err(
                ParserError::UndefinedRareConclusion(name),
                self.current_position,
            ));
        }

        let conclusion = body.conclusion.unwrap();
        let premises = body.premises.clone();

        // Whether an instantiation of this rule can need meta-rewriting depends on the rule's own
        // terms and on the argument values it is given; the first half only depends on the rule,
        // so it is decided here rather than at every step that uses the rule.
        let shapes = crate::rare::meta_shapes();
        let has_meta_construct =
            shapes.contains_redex(&conclusion) || premises.iter().any(|p| shapes.contains_redex(p));

        Ok(RuleDefinition {
            name,
            parameters: parameters.iter().cloned().collect(),
            arguments: body.args.clone(),
            premises,
            conclusion,
            is_elaborated: false,
            has_meta_construct,
        })
    }

    pub(crate) fn parse_rare(&mut self) -> CarcaraResult<Rules> {
        let mut rules = vec![];
        while self.current_token != Token::Eof {
            rules.push(self.parse_rule()?);
        }

        Ok(RareStatements {
            rules: rules
                .iter()
                .map(|x| (x.name.clone(), (*x).clone()))
                .collect(),
        })
    }
}

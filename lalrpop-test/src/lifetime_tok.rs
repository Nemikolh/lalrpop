#![allow(unused_imports)]
use lifetime_tok_lib::LtTok;
extern crate lalrpop_util as __lalrpop_util;
use self::__lalrpop_util::ParseError as __ParseError;

mod __parse__Expr {
    #![allow(non_snake_case, non_camel_case_types, unused_mut, unused_variables, unused_imports)]

    use lifetime_tok_lib::LtTok;
    extern crate lalrpop_util as __lalrpop_util;
    use self::__lalrpop_util::ParseError as __ParseError;
    use super::__ToTriple;
    pub fn parse_Expr<
        'input,
        __TOKEN: __ToTriple<'input, Error=()>,
        __TOKENS: IntoIterator<Item=__TOKEN>,
    >(
        __tokens: __TOKENS,
    ) -> Result<Vec<&'input str>, __ParseError<(),LtTok<'input>,()>>
    {
        let __tokens = __tokens.into_iter();
        let mut __tokens = __tokens.map(|t| __ToTriple::to_triple(t));
        let __lookahead = match __tokens.next() {
            Some(Ok(v)) => Some(v),
            None => None,
            Some(Err(e)) => return Err(__ParseError::User { error: e }),
        };
        match try!(__state0(&mut __tokens, __lookahead)) {
            (Some(__lookahead), _) => {
                Err(__ParseError::ExtraToken { token: __lookahead })
            }
            (None, __Nonterminal::____Expr((_, __nt, _))) => {
                Ok(__nt)
            }
            _ => unreachable!(),
        }
    }

    #[allow(dead_code)]
    pub enum __Nonterminal<'input> {
        Expr(((), Vec<&'input str>, ())),
        Other_2a(((), ::std::vec::Vec<&'input str>, ())),
        Other_2b(((), ::std::vec::Vec<&'input str>, ())),
        ____Expr(((), Vec<&'input str>, ())),
    }

    // State 0
    //   Expr = (*) [EOF]
    //   Expr = (*) Other+ [EOF]
    //   Other+ = (*) Other+ Other [EOF]
    //   Other+ = (*) Other+ Other [Other]
    //   Other+ = (*) Other [EOF]
    //   Other+ = (*) Other [Other]
    //   __Expr = (*) Expr [EOF]
    //
    //   EOF -> Reduce(Expr =  => ActionFn(6);)
    //   Other -> Shift(S3)
    //
    //   Expr -> S1
    //   Other+ -> S2
    pub fn __state0<
        'input,
        __TOKENS: Iterator<Item=Result<((), LtTok<'input>, ()),()>>,
    >(
        __tokens: &mut __TOKENS,
        __lookahead: Option<((), LtTok<'input>, ())>,
    ) -> Result<(Option<((), LtTok<'input>, ())>, __Nonterminal<'input>), __ParseError<(),LtTok<'input>,()>>
    {
        let mut __result: (Option<((), LtTok<'input>, ())>, __Nonterminal<'input>);
        match __lookahead {
            Some((__loc1, LtTok::Other(__tok0), __loc2)) => {
                let mut __sym0 = &mut Some((__loc1, (__tok0), __loc2));
                __result = try!(__state3(__tokens, __sym0));
            }
            None => {
                let __start: () = ::std::default::Default::default();
                let __end = __lookahead.as_ref().map(|o| o.0.clone()).unwrap_or_else(|| __start.clone());
                let __nt = super::__action6(&__start, &__end);
                let __nt = __Nonterminal::Expr((
                    __start,
                    __nt,
                    __end,
                ));
                __result = (__lookahead, __nt);
            }
            _ => {
                return Err(__ParseError::UnrecognizedToken {
                    token: __lookahead,
                    expected: vec![],
                });
            }
        }
        loop {
            let (__lookahead, __nt) = __result;
            match __nt {
                __Nonterminal::Expr(__nt) => {
                    let __sym0 = &mut Some(__nt);
                    __result = try!(__state1(__tokens, __lookahead, __sym0));
                }
                __Nonterminal::Other_2b(__nt) => {
                    let __sym0 = &mut Some(__nt);
                    __result = try!(__state2(__tokens, __lookahead, __sym0));
                }
                _ => {
                    return Ok((__lookahead, __nt));
                }
            }
        }
    }

    // State 1
    //   __Expr = Expr (*) [EOF]
    //
    //   EOF -> Reduce(__Expr = Expr => ActionFn(0);)
    //
    pub fn __state1<
        'input,
        __TOKENS: Iterator<Item=Result<((), LtTok<'input>, ()),()>>,
    >(
        __tokens: &mut __TOKENS,
        __lookahead: Option<((), LtTok<'input>, ())>,
        __sym0: &mut Option<((), Vec<&'input str>, ())>,
    ) -> Result<(Option<((), LtTok<'input>, ())>, __Nonterminal<'input>), __ParseError<(),LtTok<'input>,()>>
    {
        let mut __result: (Option<((), LtTok<'input>, ())>, __Nonterminal<'input>);
        match __lookahead {
            None => {
                let __sym0 = __sym0.take().unwrap();
                let __start = __sym0.0.clone();
                let __end = __sym0.2.clone();
                let __nt = super::__action0(__sym0);
                let __nt = __Nonterminal::____Expr((
                    __start,
                    __nt,
                    __end,
                ));
                return Ok((__lookahead, __nt));
            }
            _ => {
                return Err(__ParseError::UnrecognizedToken {
                    token: __lookahead,
                    expected: vec![],
                });
            }
        }
    }

    // State 2
    //   Expr = Other+ (*) [EOF]
    //   Other+ = Other+ (*) Other [EOF]
    //   Other+ = Other+ (*) Other [Other]
    //
    //   EOF -> Reduce(Expr = Other+ => ActionFn(7);)
    //   Other -> Shift(S4)
    //
    pub fn __state2<
        'input,
        __TOKENS: Iterator<Item=Result<((), LtTok<'input>, ()),()>>,
    >(
        __tokens: &mut __TOKENS,
        __lookahead: Option<((), LtTok<'input>, ())>,
        __sym0: &mut Option<((), ::std::vec::Vec<&'input str>, ())>,
    ) -> Result<(Option<((), LtTok<'input>, ())>, __Nonterminal<'input>), __ParseError<(),LtTok<'input>,()>>
    {
        let mut __result: (Option<((), LtTok<'input>, ())>, __Nonterminal<'input>);
        match __lookahead {
            Some((__loc1, LtTok::Other(__tok0), __loc2)) => {
                let mut __sym1 = &mut Some((__loc1, (__tok0), __loc2));
                __result = try!(__state4(__tokens, __sym0, __sym1));
            }
            None => {
                let __sym0 = __sym0.take().unwrap();
                let __start = __sym0.0.clone();
                let __end = __sym0.2.clone();
                let __nt = super::__action7(__sym0);
                let __nt = __Nonterminal::Expr((
                    __start,
                    __nt,
                    __end,
                ));
                return Ok((__lookahead, __nt));
            }
            _ => {
                return Err(__ParseError::UnrecognizedToken {
                    token: __lookahead,
                    expected: vec![],
                });
            }
        }
        return Ok(__result);
    }

    // State 3
    //   Other+ = Other (*) [EOF]
    //   Other+ = Other (*) [Other]
    //
    //   EOF -> Reduce(Other+ = Other => ActionFn(4);)
    //   Other -> Reduce(Other+ = Other => ActionFn(4);)
    //
    pub fn __state3<
        'input,
        __TOKENS: Iterator<Item=Result<((), LtTok<'input>, ()),()>>,
    >(
        __tokens: &mut __TOKENS,
        __sym0: &mut Option<((), &'input str, ())>,
    ) -> Result<(Option<((), LtTok<'input>, ())>, __Nonterminal<'input>), __ParseError<(),LtTok<'input>,()>>
    {
        let mut __result: (Option<((), LtTok<'input>, ())>, __Nonterminal<'input>);
        let __lookahead = match __tokens.next() {
            Some(Ok(v)) => Some(v),
            None => None,
            Some(Err(e)) => return Err(__ParseError::User { error: e }),
        };
        match __lookahead {
            None |
            Some((_, LtTok::Other(_), _)) => {
                let __sym0 = __sym0.take().unwrap();
                let __start = __sym0.0.clone();
                let __end = __sym0.2.clone();
                let __nt = super::__action4(__sym0);
                let __nt = __Nonterminal::Other_2b((
                    __start,
                    __nt,
                    __end,
                ));
                return Ok((__lookahead, __nt));
            }
            _ => {
                return Err(__ParseError::UnrecognizedToken {
                    token: __lookahead,
                    expected: vec![],
                });
            }
        }
    }

    // State 4
    //   Other+ = Other+ Other (*) [EOF]
    //   Other+ = Other+ Other (*) [Other]
    //
    //   EOF -> Reduce(Other+ = Other+, Other => ActionFn(5);)
    //   Other -> Reduce(Other+ = Other+, Other => ActionFn(5);)
    //
    pub fn __state4<
        'input,
        __TOKENS: Iterator<Item=Result<((), LtTok<'input>, ()),()>>,
    >(
        __tokens: &mut __TOKENS,
        __sym0: &mut Option<((), ::std::vec::Vec<&'input str>, ())>,
        __sym1: &mut Option<((), &'input str, ())>,
    ) -> Result<(Option<((), LtTok<'input>, ())>, __Nonterminal<'input>), __ParseError<(),LtTok<'input>,()>>
    {
        let mut __result: (Option<((), LtTok<'input>, ())>, __Nonterminal<'input>);
        let __lookahead = match __tokens.next() {
            Some(Ok(v)) => Some(v),
            None => None,
            Some(Err(e)) => return Err(__ParseError::User { error: e }),
        };
        match __lookahead {
            None |
            Some((_, LtTok::Other(_), _)) => {
                let __sym0 = __sym0.take().unwrap();
                let __sym1 = __sym1.take().unwrap();
                let __start = __sym0.0.clone();
                let __end = __sym1.2.clone();
                let __nt = super::__action5(__sym0, __sym1);
                let __nt = __Nonterminal::Other_2b((
                    __start,
                    __nt,
                    __end,
                ));
                return Ok((__lookahead, __nt));
            }
            _ => {
                return Err(__ParseError::UnrecognizedToken {
                    token: __lookahead,
                    expected: vec![],
                });
            }
        }
    }
}
pub use self::__parse__Expr::parse_Expr;

pub fn __action0<
    'input,
>(
    (_, __0, _): ((), Vec<&'input str>, ()),
) -> Vec<&'input str>
{
    (__0)
}

pub fn __action1<
    'input,
>(
    (_, __0, _): ((), ::std::vec::Vec<&'input str>, ()),
) -> Vec<&'input str>
{
    (__0)
}

pub fn __action2<
    'input,
>(
    __lookbehind: &(),
    __lookahead: &(),
) -> ::std::vec::Vec<&'input str>
{
    vec![]
}

pub fn __action3<
    'input,
>(
    (_, v, _): ((), ::std::vec::Vec<&'input str>, ()),
) -> ::std::vec::Vec<&'input str>
{
    v
}

pub fn __action4<
    'input,
>(
    (_, __0, _): ((), &'input str, ()),
) -> ::std::vec::Vec<&'input str>
{
    vec![__0]
}

pub fn __action5<
    'input,
>(
    (_, v, _): ((), ::std::vec::Vec<&'input str>, ()),
    (_, e, _): ((), &'input str, ()),
) -> ::std::vec::Vec<&'input str>
{
    { let mut v = v; v.push(e); v }
}

pub fn __action6<
    'input,
>(
    __lookbehind: &(),
    __lookahead: &(),
) -> Vec<&'input str>
{
    let __start0 = __lookbehind.clone();
    let __end0 = __lookahead.clone();
    let __temp0 = __action2(
        &__start0,
        &__end0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action1(
        __temp0,
    )
}

pub fn __action7<
    'input,
>(
    __0: ((), ::std::vec::Vec<&'input str>, ()),
) -> Vec<&'input str>
{
    let __start0 = __0.0.clone();
    let __end0 = __0.2.clone();
    let __temp0 = __action3(
        __0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action1(
        __temp0,
    )
}

pub trait __ToTriple<'input, > {
    type Error;
    fn to_triple(value: Self) -> Result<((),LtTok<'input>,()),Self::Error>;
}

impl<'input, > __ToTriple<'input, > for LtTok<'input> {
    type Error = ();
    fn to_triple(value: Self) -> Result<((),LtTok<'input>,()),()> {
        Ok(((), value, ()))
    }
}
impl<'input, > __ToTriple<'input, > for Result<(LtTok<'input>),()> {
    type Error = ();
    fn to_triple(value: Self) -> Result<((),LtTok<'input>,()),()> {
        value.map(|v| ((), v, ()))
    }
}

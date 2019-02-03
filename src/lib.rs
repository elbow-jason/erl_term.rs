#[derive(Debug)]
pub enum ErlTermError {
    InvalidBinaryFormat,
}


#[macro_use]
extern crate nom;

use nom::{be_u8, be_i32, be_u32, be_u16, be_f64, IResult};

named!(parse_small_int<&[u8], Term>, 
    do_parse!(
        tag!(&[97_u8]) >>
        value: be_u8 >> 
        (Term::SmallInt(value))
    )
);

named!(parse_small_big_int<&[u8], Term>,
    do_parse!(
        tag!(&[110_u8]) >>
        length: be_u8 >>
        sign: be_u8 >>
        content: take!(length) >>
        (Term::SmallBigInt(Sign::from_u8(sign), content.to_vec()))
    )
);

named!(parse_integer<&[u8], Term>,
    do_parse!(
        tag!(&[98_u8]) >>
        value: be_i32 >>
        (Term::Integer(value))
    )
);

named!(parse_binary<&[u8], Term>,
    do_parse!(
        tag!(&[109_u8]) >>
        value: length_bytes!(be_u32) >>
        (Term::Binary(value.to_vec()))
    )
);

named!(parse_atom<&[u8], Term>,
    do_parse!(
        tag!(&[100_u8]) >>
        value: length_bytes!(be_u16) >>
        (Term::Atom(value.to_vec()))
    )
);

named!(parse_empty<&[u8], Term>,
    do_parse!(
        tag!(&[106_u8]) >>
        (Term::Empty)
    )
);

named!(parse_f64<&[u8], Term>,
    do_parse!(
        tag!(&[70_u8]) >>
        value: be_f64 >>
        (Term::Float(value))
    )
);

named!(parse_tuple<&[u8], Term>,
    do_parse!(
        tag!(&[104_u8]) >>
        size: be_u8 >>
        items: apply!(parse_items, size as usize) >>
        (Term::Tuple(size, items))
    )
);

named!(parse_list<&[u8], Term>,
    do_parse!(
        tag!(&[108_u8]) >>
        size: be_u32 >>
        terms: apply!(parse_items, (size as usize + 1) as usize) >>
        (items_to_list(terms))
    )
);

named!(parse_map<&[u8], Term>,
    do_parse!(
        tag!(&[116_u8]) >>
        size: be_u32 >>
        pairs: apply!(parse_pairs, size as usize) >>
        (Term::Map(pairs))
    )
);

fn parse_pairs(data: &[u8], size: usize) -> IResult<&[u8], Vec<(Term, Term)>> {
    let mut pairs: Vec<(Term, Term)> = Vec::with_capacity(size);
    let mut rest = data;
    let mut count = size;
    while count > 0 {
        match parse_items(rest, 2) {
            Ok((remaining, items)) => {
                let key = items[0].clone();
                let value = items[1].clone();
                pairs.push((key, value));
                rest = remaining;
                count -= 1;

            }
            Err(e) => return Err(e),
        }
    }

    Ok((rest, pairs))
}

fn items_to_list(terms: Vec<Term>) -> Term {
    let (items, tail) = split_tail(terms);
    Term::List(items, Box::new(tail))
}

fn split_tail(terms: Vec<Term>) -> (Vec<Term>, Term) {
    let length = terms.len() as usize;
    let items = terms[..length - 1].to_vec();
    let tail = terms[length - 1].clone();
    (items, tail)
}

named!(parse_charlist<&[u8], Term>,
    do_parse!(
        tag!(&[107_u8]) >>
        size: be_u16 >>
        value: take!(size) >>
        (Term::CharList(value.to_vec()))
    )
);

#[allow(dead_code)]
fn parse_items(data: &[u8], size: usize) -> IResult<&[u8], Vec<Term>> {
    let mut parsed: Vec<Term> = Vec::with_capacity(size);
    let mut count = 0;
    let mut rest = data;
    while count < size {
        match Term::parse_headerless(rest) {
            Ok((remaining, term)) => {
                rest = remaining;
                count += 1;
                parsed.push(term);
            }
            Err(e) => return Err(e),
        }
    }
    if parsed.len() != size {
        Err(nom::Err::Incomplete(nom::Needed::Size(size)))
    } else {
        Ok((rest, parsed))
    }
    
}

fn done_or_error(res: IResult<&[u8], Term>) -> DecodeResult {
    match res {
        Ok((rest, term)) => {
            if rest.len() == 0 {
                Ok(term)
            } else {
                Term::format_error()
            }
        }
        _ => Term::format_error()
    }
    
}

type DecodeResult = Result<Term, ErlTermError>;

static ONE_THREE_ONE: u8 = 131;

#[derive(Debug, PartialEq, Clone)]
pub enum Sign {
    Pos,
    Neg,
}

impl Sign {
    fn from_u8(value: u8) -> Sign {
        match value {
            0 => Sign::Pos,
            1 => Sign::Neg,
            _ => panic!("Invalid sign value {:?}", value),
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum Term {
    SmallInt(u8),
    Integer(i32),
    Atom(Vec<u8>),
    Binary(Vec<u8>),
    Float(f64),
    Tuple(u8, Vec<Term>),
    CharList(Vec<u8>),
    List(Vec<Term>, Box<Term>),
    Empty,
    SmallBigInt(Sign, Vec<u8>),
    Map(Vec<(Term, Term)>),
}

impl Term {

    fn format_error<'a>() -> DecodeResult {
        Err(ErlTermError::InvalidBinaryFormat)
    }

    fn parse_headerless(b: &[u8]) -> IResult<&[u8], Term> {
        if b.len() == 0 {
            return Err(nom::Err::Incomplete(nom::Needed::Unknown))
        }
        let parser = match b[0] {
            97 => parse_small_int,
            98 => parse_integer,
            109 => parse_binary,
            100 => parse_atom,
            70 => parse_f64,
            104 => parse_tuple,
            107 => parse_charlist,
            108 => parse_list,
            106 => parse_empty,
            110 => parse_small_big_int,
            116 => parse_map,
            _ => return Err(nom::Err::Incomplete(nom::Needed::Unknown)),
        };
        parser(b)
    }

    pub fn from_bytes(bytes: &[u8]) -> DecodeResult {
        let byte_size: usize = bytes.len();
        if byte_size < 3 {
            return Term::format_error();
        }
        if bytes[0] != ONE_THREE_ONE {
            return Term::format_error();
        }
        let t = Term::parse_headerless(&bytes[1..]);
        done_or_error(t)
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn parse_small_int_works() {
        let bytes: Vec<u8> = vec![97, 2];
        match parse_small_int(&bytes) {
            Ok((rest, got)) => {
                assert_eq!(rest.len(), 0);
                assert_eq!(got, Term::SmallInt(2_u8));
            }
            Err(e) => {
                panic!("test failed - {:?}", e);
            }
        }
    }

    #[test]
    fn parse_integer_works() {
        let bytes: Vec<u8> = vec![98, 255, 255, 255, 255];
        match parse_integer(&bytes) {
            Ok((rest, got)) => {
                assert_eq!(rest.len(), 0);
                assert_eq!(got, Term::Integer(-1_i32));
            }
            Err(e) => {
                panic!("test failed - {:?}", e);
            }
        }
    }

    #[test]
    fn parse_binary_works() {
        let bytes: Vec<u8> = vec![109, 0, 0, 0, 5, 106, 97, 115, 111, 110];
        match parse_binary(&bytes) {
            Ok((rest, got)) => {
                assert_eq!(rest.len(), 0);
                assert_eq!(got, Term::Binary(vec![106, 97, 115, 111, 110]));
            }
            Err(e) => {
                panic!("test failed - {:?}", e);
            }
        }
    }

    #[test]
    fn parse_atom_works() {
        let bytes: Vec<u8> = vec![100, 0, 5, 106, 97, 115, 111, 110];
        match parse_atom(&bytes) {
            Ok((rest, got)) => {
                assert_eq!(rest.len(), 0);
                assert_eq!(got, Term::Atom(vec![106, 97, 115, 111, 110]));
            }
            Err(e) => {
                panic!("test failed - {:?}", e);
            }
        }
    }

    #[test]
    fn parse_items_works() {
        let items = vec![100, 0, 2, 111, 107, 97, 0];
        let ok_atom = Term::Atom(vec![111, 107]);
        let zero_small_int = Term::SmallInt(0);
        match parse_items(&items, 2) {
            Ok((rest, parsed)) => {
                assert_eq!(parsed.len(), 2);
                assert_eq!(rest.len(), 0);
                assert_eq!(parsed[0], ok_atom);
                assert_eq!(parsed[1], zero_small_int);
            }
            Err(e) => {
                panic!("test failed - {:?}", e);
            }
        }
    }


    #[test]
    fn parse_items_returns_excess_bytes() {
        let items = vec![100, 0, 2, 111, 107, 97, 0];
        match parse_items(&items, 1) {
            Ok((rest, parsed)) => {
                assert_eq!(parsed.len(), 1);
                assert_eq!(rest.to_vec(), vec![97, 0]);
                let ok_atom = Term::Atom(vec![111, 107]);
                assert_eq!(parsed[0], ok_atom);
            }
            Err(e) => {
                panic!("test failed - {:?}", e);
            }
        }
    }

    #[test]
    fn parse_items_errors_on_too_few_bytes() {
        let items = vec![100, 0, 2, 111, 107, 97, 0];
        match parse_items(&items, 3) {
            Ok(_) => panic!("test failed"),
            Err(_) => assert!(true),
        }
    }

    #[test]
    fn parse_charlist_works() {
        let bytes = vec![107, 0, 5, 106, 97, 115, 111, 110];
        match parse_charlist(&bytes) {
            Ok((rest, term)) => {
                assert_eq!(rest.len(), 0);
                assert_eq!(term, Term::CharList(vec![106, 97, 115, 111, 110]));
            }
            Err(_) => panic!("test failed"),
        }
    }

    #[test]
    fn parse_list_works() {
         
        let bytes = vec![108, 0, 0, 0, 2, 100, 0, 2, 111, 107, 100, 0, 5, 106, 97, 115, 111,
  110, 106];
        match parse_list(&bytes) {
            Ok((rest, term)) => {
                assert_eq!(rest.len(), 0);
                match term {
                    Term::List(terms, tail) => {
                        let ok_atom = Term::Atom(vec![111, 107,]);
                        let jason_atom = Term::Atom(vec![106, 97, 115, 111, 110]);
                        assert_eq!(terms.len(), 2);
                        assert_eq!(terms[0], ok_atom);
                        assert_eq!(terms[1], jason_atom);
                        assert_eq!(tail, Box::new(Term::Empty));
                    }
                    _ => panic!("test failed - parsed item was not a list")
                }
                
            }
            Err(_) => panic!("test failed"),
        }
    }

    #[test]
    fn parse_f64_works() {
        let bytes = vec![70, 63, 240, 0, 0, 0, 0, 0, 0];
        match parse_f64(&bytes) {
            Ok((rest, term)) => {
                assert_eq!(rest.len(), 0);
                assert_eq!(term, Term::Float(1.0));
            }
            Err(_) => panic!("test failed"),
        }
    }

    #[test]
    fn parse_tuple_works() {
        let bytes = vec![104, 2, 100, 0, 2, 111, 107, 97, 0];
        match parse_tuple(&bytes) {
            Ok((rest, term)) => {
                let ok_atom = Term::Atom(vec![111, 107]);
                let zero_int = Term::SmallInt(0);
                let tuple_contents = vec![
                    ok_atom,
                    zero_int,
                ];
                assert_eq!(rest.len(), 0);
                assert_eq!(term, Term::Tuple(2, tuple_contents))
            }
            Err(_) => panic!("test failed"),
        }
    }

    #[test]
    fn parse_small_big_int_works() {
        let bytes = vec![110, 5, 0, 0, 232, 118, 72, 23];
        match parse_small_big_int(&bytes) {
            Ok((rest, term)) => {
                let pos = Sign::Pos;
                assert_eq!(rest.len(), 0);
                match term {
                    Term::SmallBigInt(sign, content) => {
                        assert_eq!(sign, pos);
                        assert_eq!(content, vec![0, 232, 118, 72, 23])
                    }
                    t => panic!("test failed - wrong type {:?}", t),
                }
            }
            Err(e) => panic!("test failed - error {:?}", e),

        }
    }

    #[test]
    fn parse_empty_works() {
        let bytes: Vec<u8> = vec![106];
        match parse_empty(&bytes) {
            Ok((rest, got)) => {
                assert_eq!(rest.len(), 0);
                assert_eq!(got, Term::Empty);
            }
            Err(e) => {
                panic!("test failed - {:?}", e);
            }
        }
    }

    #[test]
    fn parse_map_works() {
        let bytes: Vec<u8> = vec![116, 0, 0, 0, 1, 100, 0, 4, 110, 97, 109, 101, 109, 0, 0, 0, 5, 106,
  97, 115, 111, 110];
        match parse_map(&bytes) {
            Ok((rest, got)) => {
                assert_eq!(rest.len(), 0);
                match got {
                    Term::Map(pairs) => {
                        assert_eq!(pairs.len(), 1);
                        let key1 = Term::Atom(vec![110, 97, 109, 101]);
                        let value1 = Term::Binary(vec![106, 97, 115, 111, 110]);
                        assert_eq!(pairs[0], (key1, value1));
                    }
                    t => panic!("test failed - unexpected term type {:?}", t),
                }
                
            }
            Err(e) => {
                panic!("test failed - {:?}", e);
            }
        }
    }
}

//
// Copyright (c) 2023 ZettaScale Technology
//
// This program and the accompanying materials are made available under the
// terms of the Eclipse Public License 2.0 which is available at
// http://www.eclipse.org/legal/epl-2.0, or the Apache License, Version 2.0
// which is available at https://www.apache.org/licenses/LICENSE-2.0.
//
// SPDX-License-Identifier: EPL-2.0 OR Apache-2.0
//
// Contributors:
//   ZettaScale Zenoh Team, <zenoh@zettascale.tech>
//


use core::cmp::min;
use std::str::FromStr;

use zenoh_result::{bail, ZError};
use std::collections::{HashMap, hash_map::Entry::Vacant, hash_map::Entry::Occupied};
use unicode_segmentation::UnicodeSegmentation;

#[derive(Clone, Debug, PartialEq)]
pub struct Trie<T: std::cmp::Eq + std::hash::Hash + Clone> {
    pub children: HashMap<T, Trie<T>>
}

impl<T: std::cmp::Eq + std::hash::Hash + Clone> Trie<T> {
    pub fn new() -> Trie<T> {
        Trie {
            children: HashMap::new()
        }
    }

    pub fn append(&mut self, part: T) -> &mut Trie<T>{
        let v = self.children.entry(part).or_insert(Trie::new());
        v
    }

    pub fn append_sequence<'a, Q: ?Sized>(&mut self, s: &[&'a Q])
    where
        T: core::borrow::Borrow<Q> + From<&'a Q> {
        if s.is_empty() {
            return;
        }
        match self.children.entry(s[0].into()) {
            Vacant(e) => { e.insert(Trie::new()).append_sequence(&s[1..]); },
            Occupied(mut e) => { e.get_mut().append_sequence(&s[1..])}
        };
    }

    pub fn merge_trie(&mut self, t: Trie<T>) {
        for (k, v) in t.children {
            match self.children.entry(k) {
                Vacant(e) => { e.insert(v); },
                Occupied(mut e) => { 
                    for (_ck, cv) in v.children {
                        e.get_mut().merge_trie(cv);
                    }
                }
            };
        }
    }

    pub fn append_tries(&mut self, tries: &[Trie<T>]) {
        if tries.is_empty() {
            return;
        }
        if self.is_empty() {
            self.children = tries[0].children.clone();
            for c in self.children.values_mut() {
                c.append_tries(&tries[1..])
            }
        } else {
            for c in self.children.values_mut() {
                c.append_tries(&tries)
            }
        }
    }

    pub fn get_subtree(&self, word: &[T]) ->Option<&Trie<T>> {
        if word.is_empty() {
            if self.is_empty() { Some(self) } else { None }
        } else if let Some(v) = self.children.get(&word[0]) {
            v.get_subtree(&word[1..])
        } else {
            None
        }
    }

    pub fn is_empty(&self) -> bool {
        self.children.is_empty()
    }
}

pub mod fields_list_arg_parsing {
    use nom::multi::separated_list1;
    use nom::branch::alt;
    use nom::bytes::complete::tag;
    use nom::IResult;
    use nom::sequence::delimited;
    use nom::bytes::complete::take_while1;
    use nom::combinator::map;
    use crate::projection::Trie;


    pub fn parse(input: &str) -> IResult<&str, Trie<String>> {
        let parser = delimited(
            tag("("), 
            separated_list1(tag(","), field_name_expr),
            tag(")")
        );
        map(parser, |s| {
            let mut t: Trie<String> = Trie::new();
            for st in s {
                t.merge_trie(st);
            }
            t
        })
        (input)
    }

    fn is_non_special_character(c: char) -> bool {
        c != '(' && c != ')' && c != '.' && c != ','
    }

    fn field_name_part(input: &str) -> IResult<&str, Trie<String>> {
        let parser = take_while1(is_non_special_character);
        map(parser, |s: &str| {
            let mut t: Trie<String> = Trie::new();
            t.append(s.to_string());
            t
        })
        (input)
    }

    fn field_name_expr(input: &str) -> IResult<&str, Trie<String>> {
        let parser = separated_list1(tag("."), alt((field_name_part, parse)));
        map(parser, |mut s| {
            let mut t = Trie::new();
            std::mem::swap(&mut t, &mut s[0]);
            t.append_tries(&s[1..]);
            t
        })
        (input)
    }

    #[test]
    fn test_parse() {
       let t = parse("(a)").unwrap().1;
       let mut t2 = Trie::<String>::new();
       t2.append_sequence(&["a"]);
       assert_eq!(t, t2);

       let t = parse("(a.b.c)").unwrap().1;
       let mut t2 = Trie::<String>::new();
       t2.append_sequence(&["a", "b", "c"]);
       assert_eq!(t, t2);

       let t = parse("(a.(b,c))").unwrap().1;
       let mut t2 = Trie::<String>::new();
       t2.append_sequence(&["a", "b"]);
       t2.append_sequence(&["a", "c"]);
       assert_eq!(t, t2);

       let t = parse("(a.b.c,c.d)").unwrap().1;
       let mut t2 = Trie::<String>::new();
       t2.append_sequence(&["a", "b", "c"]);
       t2.append_sequence(&["c", "d"]);
       assert_eq!(t, t2);
       
       let t = parse("((a,b).(c,d))").unwrap().1;
       let mut t2 = Trie::<String>::new();
       t2.append_sequence(&["a", "c"]);
       t2.append_sequence(&["a", "d"]);
       t2.append_sequence(&["b", "c"]);
       t2.append_sequence(&["b", "d"]);
       assert_eq!(t, t2);

       let t = parse("(a.(b,c.(d,e)).f)").unwrap().1;
       let mut t2 = Trie::<String>::new();
       t2.append_sequence(&["a", "b", "f"]);
       t2.append_sequence(&["a", "c", "d", "f"]);
       t2.append_sequence(&["a", "c", "e", "f"]);
       assert_eq!(t, t2);
   }
}

pub mod slice_arg_parsing {
    use nom::bytes::complete::tag;
    use nom::sequence::{delimited, separated_pair};
    use nom::character::complete::digit1;
    use nom::IResult;
    use nom::combinator::map_res;

    fn num(input: &str) -> IResult<&str, usize> {
        map_res(digit1, |s: &str| s.parse::<usize>())
        (input)
    }
    pub fn parse(input: &str) -> IResult<&str, (usize, usize)> {
        delimited(
            tag("("), 
            separated_pair(num, tag(","), num),
            tag(")")
        )
        (input)
    }

    #[test]
    fn test_parse() {
       assert_eq!(parse("(1,2)"), Ok(("", (1,2))));
       assert!(parse("(1a,2)").is_err());
   }
}



pub mod json_scan {
    use core::str::CharIndices;
    use core::iter::Peekable;
    use crate::projection::Trie;
    pub type Err = String;
    type Iter<'a> = Peekable<CharIndices<'a>>;
    type Intervals = Vec<(usize, usize)>;

    pub struct JsonScanner<'a> {
        data: &'a str
    }

    const ARRAY_START: char = '[';
    const ARRAY_END: char = ']';
    const DICT_START: char = '{';
    const DICT_END: char = '}';
    const ELEMENT_SEPARATOR: char = ',';
    const STRING_DELIMITER: char = '"';
    const KEY_VALUE_SEPARATOR: char = '"';
    const ESCAPE_CHAR: char = '\\';
    const IGNORED_CHARS: &[char] = &[' ', '\r', '\n', '\t'];
    
    impl<'a> JsonScanner<'a> {
        pub fn new(data: &'a str) -> JsonScanner<'a> {
            JsonScanner {
                data
            }
        }

        fn get_byte_offset(&self, ci: &mut Iter<'a>) -> usize {
            match ci.peek() {
                None => self.data.len(),
                Some(&(pos, _c)) => pos
            }
        }

        fn skip_ignored_chars(&self, mut ci: Iter<'a>) -> Iter<'a> {
            while let Some(&(_pos, c)) = ci.peek() {
                if !IGNORED_CHARS.contains(&c) { break; }
                ci.next();
            }
            return ci;
        }

        fn try_parse_char(&self, c: char, mut ci: Iter<'a>) -> Result<Option<Iter<'a>>, Err> {
            ci = self.skip_ignored_chars(ci);
            match ci.peek() {
                None => Err("unexpected end of file".to_string()),
                Some(&(_pos, cc)) => { 
                    if cc == c { ci.next(); return Ok(Some(ci)); }
                    else { return Ok(None); }
                }
            }    
        }

        fn try_parse_string(&self, mut ci: Iter<'a>) -> Result<Option<Iter<'a>>, Err> {
            ci = self.skip_ignored_chars(ci);
            match self.try_parse_char(STRING_DELIMITER, ci)? {
                Some(cci) => { ci = cci; },
                None => { return Ok(None); }
            }
    
            let mut is_escape = false;
            while let Some((_, c)) = ci.next() {
                if !is_escape && c == STRING_DELIMITER { return Ok(Some(ci)); }
                else if is_escape { is_escape = false; }
                else if c == ESCAPE_CHAR { is_escape = true; }
            }
            return Err("unexpected end of file, while parsing a string value".to_string());
        }

        fn try_parse_scalar(&self, mut ci: Iter<'a>) -> Result<Option<Iter<'a>>, Err> {
            // this function is trying to parse non-string literals (i.e. either numbers or true/false/nul - constants)
            // it does not perform any validity check
            ci = self.skip_ignored_chars(ci);
            let mut is_empty: bool = true;
            while let Some(&(_pos, c)) = ci.peek() {
                if IGNORED_CHARS.contains(&c) || c == ELEMENT_SEPARATOR || c == ARRAY_END || c == DICT_END { 
                    break;
                } else {
                    is_empty = false;
                }
                ci.next();
            }
            return if is_empty { Ok(None) } else { Ok(Some(ci)) };
        }

        fn try_parse_dict(&self, t: &Trie<String>, is_top: bool, mut ci: Iter<'a>) -> Result<Option<(Iter<'a>, Intervals)>, Err> {
            ci = self.skip_ignored_chars(ci);
            let start_offset = self.get_byte_offset(&mut ci);
            match self.try_parse_char(DICT_START, ci)? {
                Some(res) => { ci = res; },
                None => { return Ok(None); }
            }
            if let Some(res) = self.try_parse_char(DICT_END, ci.clone())? { // check if reached dict end
                return Ok(Some((res, Intervals::new())));
            }
            let mut intervals = vec![(start_offset, start_offset + 1)];
            let mut comma_offset: Option<usize> = None;
            loop {
                let (res, mut inner_intervals) = self.parse_key_value(t, ci)?;
                ci = res;
                if !t.is_empty() {
                    if !inner_intervals.is_empty() && comma_offset.is_some() && intervals.len() > 1 {
                        intervals.push((comma_offset.unwrap(), comma_offset.unwrap() + 1))
                    }
                    intervals.append(&mut inner_intervals); 
                }
                // now we either reached the end of the dict, or there is at least one more kv, which should be preceded by ','
                ci = self.skip_ignored_chars(ci);
                let end_pos = self.get_byte_offset(&mut ci);
                if let Some(mut res) = self.try_parse_char(DICT_END, ci.clone())? { // check if reached dict end
                    if t.is_empty() && !is_top { 
                        let end_pos = self.get_byte_offset(&mut res);
                        return Ok(Some((res, vec![(start_offset, end_pos)]))); 
                    } else if intervals.len() == 1 && !is_top { // none of inner fields match trie -> do not copy anything
                        return Ok(Some((res, Intervals::new()))); 
                    } else {
                        intervals.push((end_pos, end_pos + 1));
                        return Ok(Some((res, intervals)));
                    }
                }
                ci = self.skip_ignored_chars(ci);
                comma_offset = Some(self.get_byte_offset(&mut ci));
                match self.try_parse_char(ELEMENT_SEPARATOR, ci)? { // check if there is next kv
                    None => { return Err(format!("did not find '{ELEMENT_SEPARATOR}' or '{DICT_END}' after key-value").to_string()); },
                    Some(res) => { ci = res; }
                }
            }

        }

        fn try_parse_array(&self, t: &Trie<String>, is_top: bool, mut ci: Iter<'a>) -> Result<Option<(Iter<'a>, Intervals)>, Err> {
            ci = self.skip_ignored_chars(ci);
            let start_offset = self.get_byte_offset(&mut ci);
            match self.try_parse_char(ARRAY_START, ci)? {
                Some(res) => { ci = res; },
                None => { return Ok(None); }
            }
            if let Some(res) = self.try_parse_char(ARRAY_END, ci.clone())? { // check if reached array end
                return Ok(Some((res, Intervals::new())));
            }
            let mut intervals = vec![(start_offset, start_offset + 1)];
            let mut comma_offset: Option<usize> = None;
            loop {
                let (res, mut inner_intervals) =  self.parse_value(t, is_top, ci)?;
                ci = res;
                if !t.is_empty() {
                    if !inner_intervals.is_empty() && comma_offset.is_some() && intervals.len() > 1 {
                        intervals.push((comma_offset.unwrap(), comma_offset.unwrap() + 1))
                    }
                    intervals.append(&mut inner_intervals); 
                }
                // now we either reached the end of the array, or there is at least one more value, which should be preceded by ','
                ci = self.skip_ignored_chars(ci);
                let end_pos = self.get_byte_offset(&mut ci);
                if let Some(mut res) = self.try_parse_char(ARRAY_END, ci.clone())? { // check if reached array end
                    if t.is_empty() && !is_top { 
                        let end_pos = self.get_byte_offset(&mut res);
                        return Ok(Some((res, vec![(start_offset, end_pos)]))); 
                    } else if intervals.len() == 1 && !is_top { // none of inner fields match trie -> do not copy anything
                        return Ok(Some((res, Intervals::new())));
                    } else {
                        intervals.push((end_pos, end_pos + 1));
                        return Ok(Some((res, intervals)));
                    }
                }
                ci = self.skip_ignored_chars(ci);
                comma_offset = Some(self.get_byte_offset(&mut ci));
                match self.try_parse_char(ELEMENT_SEPARATOR, ci)? { // check if there is next kv
                    None => { return Err(format!("did not find '{ELEMENT_SEPARATOR}' or '{ARRAY_END}' after value").to_string()); },
                    Some(res) => { ci = res; }
                }
            }
        }

        fn try_parse_literal(&self, t: &Trie<String>, mut ci: Iter<'a>) -> Result<Option<(Iter<'a>, Intervals)>, Err> {
            let literal_start_offset = self.get_byte_offset(&mut ci);
            let mut res = self.try_parse_string(ci.clone())?;
            if res.is_none() { res = self.try_parse_scalar(ci)?; }
            match res {
                Some(mut res) => {
                    if t.is_empty() {
                        let literal_end_offset = self.get_byte_offset(&mut res);
                        return Ok(Some((res, vec![(literal_start_offset, literal_end_offset)]))); 
                    }
                    else { return Ok(Some((res, Intervals::new()))); } // since literals do not have inner fields -> return nothing
                },
                None => { return Ok(None); }
            }
        }

        fn parse_value(&self, t: &Trie<String>, is_top: bool, mut ci: Iter<'a>) -> Result<(Iter<'a>, Intervals), Err> {
            // we try to parse value: it is either string, scalar, dict or array,
            ci = self.skip_ignored_chars(ci);
            
            if let Some(res) = self.try_parse_dict(t, is_top, ci.clone())? {
                return Ok(res);
            } else if let Some(res) = self.try_parse_array(t, is_top, ci.clone())? {
                return Ok(res);
            } else if is_top {
                return Err("json top data should be either a dictionary or an array".to_string());
            } else if let Some(res) = self.try_parse_literal(t, ci)? {
                return Ok(res);
            } else {
                return Err("failed to parse value".to_string());
            }
        }

        fn parse_key_value(&self, t: &Trie<String>, mut ci: Iter<'a>) -> Result<(Iter<'a>, Intervals), Err> {
            ci = self.skip_ignored_chars(ci);
            let start_key_offset = self.get_byte_offset(&mut ci);
            match self.try_parse_string(ci)? {
                Some(res) => { ci = res; },
                None => { return Err("did not find key".to_string()); } 
            }
            let end_key_offset = self.get_byte_offset(&mut ci);
            let key = &self.data[start_key_offset + 1 .. end_key_offset - 1];
            match self.try_parse_char(':', ci)? {
                Some(res) => { ci = res; }
                None => return Err(format!("did not find '{KEY_VALUE_SEPARATOR}'").to_string())
            }
            ci = self.skip_ignored_chars(ci);
            let start_value_offset = self.get_byte_offset(&mut ci);
            match t.children.get(key) {
                None => {
                    let (res, _) = self.parse_value(&Trie::<String>::new(), false, ci)?;
                    return Ok((res, Intervals::new()));
                },
                Some(ct) => {
                    let (mut res, mut inner_intervals) = self.parse_value(ct, false, ci.clone())?;
                    if ct.is_empty() { // key is the leaf node -> copy kv entirely
                        let end_value_offset = self.get_byte_offset(&mut res);
                        return Ok((res, vec![(start_key_offset, end_value_offset)]));
                    } else { // key is an intermediate node -> copy only "key" + ':' + all eventual intervals returned by parse_value
                        let mut intervals = Intervals::new();
                        if !inner_intervals.is_empty() {
                            intervals.push((start_key_offset, start_value_offset));
                            intervals.append(&mut inner_intervals);
                        }
                        return Ok((res, intervals));
                    }
                }
            }                  
        }

        pub fn scan(&self, t: &Trie<String>) -> Result<Intervals, Err> {
            Ok(self.parse_value(t, true, self.data.char_indices().peekable())?.1)
        }
    }

 
    mod tests {
        #[cfg(test)]
        fn parse_json<'a>(t: &super::Trie<String>, json: &'a str) -> Result<String, super::Err> {
            let jsc = super::JsonScanner::new(json);
            let intervals = jsc.scan(t)?;
            let mut s = String::new();
            for i in intervals {
                s.push_str(&json[i.0..i.1]);
            }
            Ok(s)
        }

        #[cfg(test)]
        fn remove_skipped_chars(mut s: String) -> String {
            s.retain(|c| !" \r\n\t'".contains(c));
            s
        }

        #[test]
        fn test_parse_json() {
            let mut t = super::Trie::new();
            t.append_sequence(&["a"]);
            t.append_sequence(&["d", "f"]);
            t.append_sequence(&["c"]);
            t.append_sequence(&["e", "a"]);
            t.append_sequence(&["e", "b"]);
            t.append_sequence(&["a", "g"]);
            let json = r#"{
                "a" : {},
                "b" : "abc",
                "c" : [ true, false ],
                "d" : {"e" : 1, "f" : "xxx"},
                "e" : [
                    {
                        "a" : 10,
                        "b" : "xxx\""
                    },
                    {
                        "a" : 11,
                        "c" : "yyy"
                    }
                ]
            }"#;
            let json_expected = r#"{
                "c" : [ true, false ],
                "d" : {"f" : "xxx"},
                "e" : [
                    {
                        "a" : 10,
                        "b" : "xxx\""
                    },
                    {
                        "a" : 11
                    }
                ]
            }"#.to_string();
            let res = parse_json(&t, json);
            assert!(res.is_ok());
            let res = res.unwrap();

            assert_eq!(remove_skipped_chars(res), remove_skipped_chars(json_expected));
        }
    }
}


pub const PROJECTION_RULE_NAME_SLICE: &str = "slice";
pub const PROJECTION_RULE_NAME_PICK: &str = "pick";

#[derive(Debug, Clone, PartialEq)]
pub struct ProjectionSlice {
    offset: usize,
    length: usize
}

impl FromStr for ProjectionSlice {
    type Err = ZError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match slice_arg_parsing::parse(s) {
            Ok((_, (offset, length))) => {
                Ok(
                    ProjectionSlice {
                        offset,
                        length
                    }
                )
            },
            Err(e) => {
                bail!("Failed to parse projection 'slice': {}", e)
            } 
        }
    }
}

impl ProjectionSlice {
    pub fn project_bytes(&self, bytes: &[u8]) -> Result<Vec<(usize, usize)>, ZError> {
        let start = min(self.offset, bytes.len());
        let end = min(self.offset + self.length, bytes.len());
        Ok(vec![(start, end)])
    }

    pub fn project_utf8_string(&self, s: &str) -> Result<Vec<(usize, usize)>, ZError> {
        if self.length == 0 {
            return Ok(vec![(0, 0)]);
        }
        let buf_len = s.len();
        let mut grapheme_indicies = s.grapheme_indices(true);
        let start = match grapheme_indicies.nth(self.offset) {
            Some(gi) => gi.0,
            None => buf_len
        };
        let end = match grapheme_indicies.nth(self.length - 1) {
            Some(gi) => gi.0,
            None => buf_len
        };
        Ok(vec![(start, end)])
    }
}


#[derive(Debug, Clone, PartialEq)]
pub struct ProjectionPick {
    fields_trie: Trie<String>
}

impl ProjectionPick {
    pub fn project_json(&self, json: &str) -> Result<Vec<(usize, usize)>, ZError> {
        let jsc = json_scan::JsonScanner::new(json);
        match jsc.scan(&self.fields_trie) {
            Ok(intervals) => Ok(intervals),
            Err(e) => bail!("Failed to apply projection 'pick': {}", e)
        }
    }
}

impl FromStr for ProjectionPick {
    type Err = ZError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match fields_list_arg_parsing::parse(s) {
            Ok((_, fields_trie)) => {
                Ok(ProjectionPick{ fields_trie })
            },
            Err(e) => {
                bail!("Failed to parse projection 'pick': {}", e)
            } 
        }
    }
}

pub enum ProjectionRule {
    ProjectionSlice(ProjectionSlice),
    ProjectionPick(ProjectionPick),
    None
}

impl FromStr for ProjectionRule {
    type Err = ZError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s.find('(') {
            Some(index) => {
                let rule_name = &s[0..index];
                let rule_args = &s[index..];
                match rule_name {
                    PROJECTION_RULE_NAME_PICK => { 
                        return Ok(ProjectionRule::ProjectionPick(rule_args.parse()?));
                    },
                    PROJECTION_RULE_NAME_SLICE => { 
                        return Ok(ProjectionRule::ProjectionSlice(rule_args.parse()?));
                    },
                     _ => bail!("Unsupported projection rule: {}", &rule_name)
                }
            },
            None => bail!("Failed to parse projection rule, it should be in the form: 'projection_rule_name(arg1,arg2,...)'")
        }
    }
}
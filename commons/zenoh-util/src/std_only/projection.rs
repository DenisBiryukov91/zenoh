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


use std::str::FromStr;

use zenoh_result::{bail, ZError};
use std::collections::{HashMap, HashSet, hash_map::Entry::Vacant, hash_map::Entry::Occupied};

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

    pub fn append_sequence(&mut self, s: &[T]) {
        if s.is_empty() {
            return;
        }
        match self.children.entry(s[0].clone()) {
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


    pub fn parse(input: &str) -> IResult<&str, Trie<&str>> {
        let parser = delimited(
            tag("("), 
            separated_list1(tag(","), field_name_expr),
            tag(")")
        );
        map(parser, |s| {
            let mut t: Trie<&str> = Trie::new();
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

    fn field_name_part(input: &str) -> IResult<&str, Trie<&str>> {
        let parser = take_while1(is_non_special_character);
        map(parser, |s| {
            let mut t: Trie<&str> = Trie::new();
            t.append(s);
            t
        })
        (input)
    }

    fn field_name_expr(input: &str) -> IResult<&str, Trie<&str>> {
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
       let mut t2 = Trie::<&str>::new();
       t2.append_sequence(&["a"]);
       assert_eq!(t, t2);

       let t = parse("(a.b.c)").unwrap().1;
       let mut t2 = Trie::<&str>::new();
       t2.append_sequence(&["a", "b", "c"]);
       assert_eq!(t, t2);

       let t: Trie<&str> = parse("(a.(b,c))").unwrap().1;
       let mut t2 = Trie::<&str>::new();
       t2.append_sequence(&["a", "b"]);
       t2.append_sequence(&["a", "c"]);
       assert_eq!(t, t2);

       let t = parse("(a.b.c,c.d)").unwrap().1;
       let mut t2 = Trie::<&str>::new();
       t2.append_sequence(&["a", "b", "c"]);
       t2.append_sequence(&["c", "d"]);
       assert_eq!(t, t2);
       
       let t = parse("((a,b).(c,d))").unwrap().1;
       let mut t2 = Trie::<&str>::new();
       t2.append_sequence(&["a", "c"]);
       t2.append_sequence(&["a", "d"]);
       t2.append_sequence(&["b", "c"]);
       t2.append_sequence(&["b", "d"]);
       assert_eq!(t, t2);

       let t = parse("(a.(b,c.(d,e)).f)").unwrap().1;
       let mut t2 = Trie::<&str>::new();
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

pub mod json_scanner {
    use core::str::CharIndices;
    use core::iter::Peekable;
    use crate::projection::Trie;
    use crate::projection::fields_list_arg_parsing::parse;
    type Err = String;
    type Iter<'a> = Peekable<CharIndices<'a>>;
    type Intervals = Vec<(usize, usize)>;

    fn get_pos<'a>(s: &'a str, ci: &mut Iter<'a>) -> usize {
        match ci.peek() {
            None => s.len(),
            Some(&(pos, _c)) => pos
        }
    }

    fn is_ignored(c: char) -> bool {
        return c == ' ' || c == '\r' || c == '\n' || c == '\t';
    }

    fn skip_ignored(mut ci: Iter<'_>) -> Iter<'_> {
        while let Some(&(_pos, c)) = ci.peek() {
            if !is_ignored(c) { break; }
            ci.next();
        }
        return ci;
    }

    fn try_parse_char(c: char, mut ci: Iter<'_>) -> Result<Option<Iter<'_>>, Err> {
        ci = skip_ignored(ci);
        match ci.peek() {
            None => Err("found end of string".to_string()),
            Some(&(_pos, cc)) => { 
                if cc == c { ci.next(); return Ok(Some(ci)); }
                else {return Ok(None); }
            }
        }    
    }

    fn try_parse_string(mut ci: Iter<'_>) -> Result<Option<Iter<'_>>, Err> {
        ci = skip_ignored(ci);
        match try_parse_char('"', ci)? {
            Some(cci) => { ci = cci; },
            None => { return Ok(None); }
        }

        let mut is_escape = false;
        while let Some((_, c)) = ci.next() {
            if !is_escape && c == '"' { return Ok(Some(ci)) }
            else if is_escape { is_escape = false; }
            else if c == '\\' { is_escape = true; }
        }
        return Err("incomplete string".to_string());
    }

    fn try_parse_scalar(mut ci: Iter<'_>) -> Result<Option<Iter<'_>>, Err> {
        ci = skip_ignored(ci);
        let mut found_character = false;
        while let Some(&(_pos, c)) = ci.peek() {
            if is_ignored(c) || c == ',' || c == ']' || c == '}' { 
                return if found_character { Ok(Some(ci)) } else { Ok(None) };
            } else {
                found_character = true;
            }
            ci.next();
        }
        return if found_character { Ok(Some(ci)) } else { Ok(None) };
    }

    fn try_parse_object<'a, 'b>(t: &Trie<&'a str>, s: &'b str, is_top: bool, mut ci: Iter<'b>) -> Result<Option<(Iter<'b>, Intervals)>, Err> {
        ci = skip_ignored(ci);
        let mut start = ci.clone();
        let mut res = try_parse_char('{', ci)?;
        if res.is_none() { return Ok(None); };
        ci = res.unwrap();
        res = try_parse_char('}', ci.clone())?; // check if reached object end
        if res.is_some() { return Ok(Some((res.unwrap(), Intervals::new()))); }
        let mut intervals = vec![(get_pos(s, &mut start), get_pos(s, &mut start) + 1)];
        let mut comma_pos: Option<usize> = None;
        loop {
            match try_parse_kv(t, s, ci)? {
                Some((cci, mut inner_intervals)) => { 
                    ci = cci;
                    if !t.is_empty() {
                        if !inner_intervals.is_empty() && comma_pos.is_some() && intervals.len() > 1 {
                            intervals.push((comma_pos.unwrap(), comma_pos.unwrap() + 1))
                        }
                        intervals.append(&mut inner_intervals); 
                    }
                },
                None => { return Err("failed to parse key-value".to_string()); }
            }
            // now we either reached the end of the object, or there is at least one more kv, which should be preceded by ','
            ci = skip_ignored(ci);
            let end_pos = get_pos(s, &mut ci);
            res = try_parse_char('}', ci.clone())?; // check if reached object end
            if res.is_some() {
                if t.is_empty() && !is_top { 
                    let mut res = res.unwrap();
                    let end_pos = get_pos(s, &mut res);
                    return Ok(Some((res, vec![(get_pos(s, &mut start), end_pos)]))); 
                } else if intervals.len() == 1 && !is_top { // none of inner fields match trie -> do not copy anything
                    return Ok(Some((res.unwrap(), Intervals::new()))); 
                } else {
                    intervals.push((end_pos, end_pos + 1));
                    return Ok(Some((res.unwrap(), intervals)));
                }
            }
            ci = skip_ignored(ci);
            comma_pos = Some(get_pos(s, &mut ci));
            res = try_parse_char(',', ci)?; // check if there is next kv
            if res.is_none() { return Err("did not find ',' or '}' after key-value".to_string()); }
            else { ci = res.unwrap(); }
        }
    }

    fn try_parse_array<'a, 'b>(t: &Trie<&'a str>, s: &'b str, is_top: bool, mut ci: Iter<'b>) -> Result<Option<(Iter<'b>, Intervals)>, Err> {
        ci = skip_ignored(ci);
        let mut start = ci.clone();
        let mut res = try_parse_char('[', ci)?;
        if res.is_none() { return Ok(None); };
        ci = res.unwrap();
        res = try_parse_char(']', ci.clone())?; // check if reached array end
        if res.is_some() { return Ok(Some((res.unwrap(), Intervals::new()))); }
        let mut intervals = vec![(get_pos(s, &mut start), get_pos(s, &mut start) + 1)];
        let mut comma_pos: Option<usize> = None;
        loop {
            match try_parse_value(t, s, false, ci)? {
                Some((cci, mut inner_intervals)) => { 
                    ci = cci;
                    if !t.is_empty() {
                        if !inner_intervals.is_empty() && comma_pos.is_some() && intervals.len() > 1 {
                            intervals.push((comma_pos.unwrap(), comma_pos.unwrap() + 1))
                        }
                        intervals.append(&mut inner_intervals); 
                    }
                },
                None => { return Err("failed to parse value".to_string()); }
            }
            // now we either reached the end of the array, or there is at least one value, which should be preceded by ','
            ci = skip_ignored(ci);
            let end_pos = get_pos(s, &mut ci);
            res = try_parse_char(']', ci.clone())?; // check if reached array end
            if res.is_some() {
                if t.is_empty() && !is_top {
                    let mut res = res.unwrap();
                    let end_pos = get_pos(s, &mut res);
                    return Ok(Some((res, vec![(get_pos(s, &mut start), end_pos)]))); 
                } else if intervals.len() == 1 && !is_top { // none of inner fields match trie -> do not copy anything
                    return Ok(Some((res.unwrap(), Vec::<(usize, usize)>::new())));
                } else {
                    intervals.push((end_pos, end_pos + 1));
                    return Ok(Some((res.unwrap(), intervals)));
                }
            }
            ci = skip_ignored(ci);
            comma_pos = Some(get_pos(s, &mut ci));
            res = try_parse_char(',', ci)?; // check if there is next value
            if res.is_none() { return Err("did not find ',' or ']' after value".to_string()); }
            else { ci = res.unwrap(); }
        }
    }

    fn try_parse_value<'a, 'b>(t: &Trie<&'a str>, s: &'b str, is_top: bool, mut ci: Iter<'b>) -> Result<Option<(Iter<'b>, Intervals)>, Err> {
        // we try to parse value: it is either string, scalar, object or array,
        ci = skip_ignored(ci);
        
        let mut res = try_parse_object(t, s, is_top, ci.clone())?;
        if res.is_none() { res = try_parse_array(t, s, is_top, ci.clone())?; }
        if !res.is_none() { return Ok(res); };
        if is_top {
            return Err("json object should be either a dictionary or an array".to_string());
        }
        let mut start = ci.clone();
        let mut res = try_parse_string(ci.clone())?;
        if res.is_none() { res = try_parse_scalar(ci)?; }
        if res.is_none() { return Err("failed to parse value".to_string()); } 
        if t.is_empty() {
            let mut res = res.unwrap();
            let end_pos = get_pos(s, &mut res);
            return Ok(Some((res, vec![(get_pos(s, &mut start), end_pos)]))); 
        }
        else { return Ok(Some((res.unwrap(), Intervals::new()))); }
    }

    fn try_parse_kv<'a, 'b>(t: &Trie<&'a str>, s: &'b str, mut ci: Iter<'b>) -> Result<Option<(Iter<'b>, Intervals)>, Err> {
        ci = skip_ignored(ci);
        let mut start_key = ci.clone();
        let res = try_parse_string(ci)?;
        if res.is_none() { return Err("did not find key".to_string()); }
        ci = res.unwrap();
        let key = &s[get_pos(s, &mut start_key) + 1 .. get_pos(s, &mut ci) - 1];
        let res = try_parse_char(':', ci)?;
        if res.is_none() { return Err("did not find ':'".to_string())};
        let mut start_value = skip_ignored(res.unwrap());
        let tc = t.children.get(&key);
        if tc.is_none() {
            match try_parse_value(&Trie::<&'a str>::new(), s, false, start_value)? {
                None => Ok(None),
                Some((res, _)) => Ok(Some((res, Intervals::new())))
            }
        } else {
            let (mut end_value, mut inner_intervals) = try_parse_value(tc.unwrap(), s, false, start_value.clone())?.unwrap();
            if tc.unwrap().is_empty() { // key is the leaf node -> copy kv entirely
                let end_pos = get_pos(s, &mut end_value);
                return Ok(Some((end_value, vec![(get_pos(s, &mut start_key), end_pos)])));
            } else { // key is an intermediate node -> copy only "key" + : + all eventual intervals returned by parse_value
                let mut intervals = Intervals::new();
                if !inner_intervals.is_empty() {
                    intervals.push((get_pos(s, &mut start_key), get_pos(s, &mut start_value)));
                    intervals.append(&mut inner_intervals);
                }
                return Ok(Some((end_value, intervals)));
            }
        }
    }

    fn parse_json<'a, 'b>(t: &Trie<&'a str>, json: &'b str) -> Result<String, Err> {
        let res = try_parse_value(t, json, true, json.char_indices().peekable());
        match res {
            Err(e) => Err(e),
            Ok(o) => {
                match o {
                    None => Err("failed to parse".to_string()),
                    Some((_ci, intervals)) => {
                        let mut s = String::new();
                        for i in intervals {
                            s.push_str(&json[i.0..i.1]);
                        }
                        Ok(s)
                    }
                }
            }
        }
    }
    #[test]
    fn test_parse_json() {
        let mut t = Trie::new();
        // t.append_sequence(&["a"]);
        // t.append_sequence(&["d", "f"]);
        // t.append_sequence(&["c"]);
        // t.append_sequence(&["e", "a"]);
        // t.append_sequence(&["e", "b"]);
        // t.append_sequence(&["a", "g"]);
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
        let res = parse_json(&t, json);
        assert!(res.is_ok());
        assert_eq!(res.unwrap().as_str(), "abc");
    }
    /*#[test]
    fn test_parse_char() {
        let res = try_parse_char('a', "  ab".char_indices().peekable());
        assert!(res.is_ok());
        let res = res.unwrap();
        assert!(res.is_some());
        assert_eq!(res.unwrap().peek(), Some(&(3,'b')));

        let res = try_parse_char('c', "  ab".char_indices().peekable());
        assert!(res.is_ok());
        let res = res.unwrap();
        assert!(res.is_none());

        let res = try_parse_char('c', "  ".char_indices().peekable());
        assert!(res.is_err());
   }

   #[test]
   fn test_parse_string() {
       let res = try_parse_string(r#"  "abc", "#.char_indices().peekable());
       assert!(res.is_ok());
       let res = res.unwrap();
       assert!(res.is_some());
       assert_eq!(res.unwrap().peek(), Some(&(7,',')));

       let res = try_parse_string(r#"  "ab\"d","#.char_indices().peekable());
       assert!(res.is_ok());
       let res = res.unwrap();
       assert!(res.is_some());
       assert_eq!(res.unwrap().peek(), Some(&(9,',')));

       let res = try_parse_string(r#"  abc","#.char_indices().peekable());
       assert!(res.is_ok());
       let res = res.unwrap();
       assert!(res.is_none());

       let res = try_parse_string(r#"  "abc"#.char_indices().peekable());
       assert!(res.is_err());
  }

  #[test]
    fn test_parse_scalar() {
        let res: Result<Option<Peekable<CharIndices<'_>>>, String> = try_parse_scalar("  abc, ".char_indices().peekable());
        assert!(res.is_ok());
        let res = res.unwrap();
        assert!(res.is_some());
        assert_eq!(res.unwrap().peek(), Some(&(5,',')));

        let res = try_parse_scalar("  abc ,".char_indices().peekable());
        assert!(res.is_ok());
        let res = res.unwrap();
        assert!(res.is_some());
        assert_eq!(res.unwrap().peek(), Some(&(5,' ')));

        let res = try_parse_scalar("  ".char_indices().peekable());
        assert!(res.is_ok());
        let res = res.unwrap();
        assert!(res.is_none());
    }

    #[test]
    fn test_parse_kv() {
        let res: Result<Option<Peekable<CharIndices<'_>>>, String> = try_parse_kv(r#"  "abc" : "cde", "#.char_indices().peekable());
        assert!(res.is_ok());
        let res = res.unwrap();
        assert!(res.is_some());
        assert_eq!(res.unwrap().peek(), Some(&(15,',')));

        let res = try_parse_kv(r#"  "abc": 10 "#.char_indices().peekable());
        assert!(res.is_ok());
        let res = res.unwrap();
        assert!(res.is_some());
        assert_eq!(res.unwrap().peek(), Some(&(11,' ')));

        let res = try_parse_kv(r#"  "abc" "#.char_indices().peekable());
        assert!(res.is_err());

        let res = try_parse_kv(r#"  "abc" : "#.char_indices().peekable());
        assert!(res.is_err());
    }

    #[test]
    fn test_parse_object() {
        let json = r#"{}$"#;
        let res: Result<Option<Peekable<CharIndices<'_>>>, String> = try_parse_object(json.char_indices().peekable());
        assert!(res.is_ok());
        let res = res.unwrap();
        assert!(res.is_some());
        assert_eq!(res.unwrap().peek(), Some(&(json.len() - 1,'$')));

        let json = r#"{
            "key1" : "value",
            "key2" : 10,
            "key3" : true
        }$"#;
        let res: Result<Option<Peekable<CharIndices<'_>>>, String> = try_parse_object(json.char_indices().peekable());
        assert!(res.is_ok());
        let res = res.unwrap();
        assert!(res.is_some());
        assert_eq!(res.unwrap().peek(), Some(&(json.len() - 1,'$')));

        let json = r#"{
            "key1" : "value",
            "key2" : { "inner_key1" : 1 },
            "key3" : { "inner_key2" : "abc", "inner_key3": null }
        }$"#;
        let res: Result<Option<Peekable<CharIndices<'_>>>, String> = try_parse_object(json.char_indices().peekable());
        assert!(res.is_ok());
        let res = res.unwrap();
        assert!(res.is_some());
        assert_eq!(res.unwrap().peek(), Some(&(json.len() - 1,'$')));

        let json = r#"{
            "key1" : "value",
            "key2" : 10
            "key3" : true
        }"#;
        let res: Result<Option<Peekable<CharIndices<'_>>>, String> = try_parse_object(json.char_indices().peekable());
        assert!(res.is_err());

        let json = r#"{
            "key1" : "value",
            "key2" : 10,
            "key3" : true
        "#;
        let res: Result<Option<Peekable<CharIndices<'_>>>, String> = try_parse_object(json.char_indices().peekable());
        assert!(res.is_err());

        let json = r#"{
            "key1" : "value",
            "key2" : { "inner_key1" : 1 },
            "key3" : { "inner_key2" : "abc", "inner_key3": null 
        }$"#;
        let res: Result<Option<Peekable<CharIndices<'_>>>, String> = try_parse_object(json.char_indices().peekable());
        assert!(res.is_err());
    }

    #[test]
    fn test_parse_array() {
        let json = r#"[]$"#;
        let res: Result<Option<Peekable<CharIndices<'_>>>, String> = try_parse_array(json.char_indices().peekable());
        assert!(res.is_ok());
        let res = res.unwrap();
        assert!(res.is_some());
        assert_eq!(res.unwrap().peek(), Some(&(json.len() - 1,'$')));

        let json = r#"[ "abc", 1, true]$"#;
        let res: Result<Option<Peekable<CharIndices<'_>>>, String> = try_parse_array(json.char_indices().peekable());
        assert!(res.is_ok());
        let res = res.unwrap();
        assert!(res.is_some());
        assert_eq!(res.unwrap().peek(), Some(&(json.len() - 1,'$')));

        let json = r#"[
            10,
            "string", 
            {
                "key1" : "value",
                "key2" : { "inner_key1" : 1 },
                "key3" : { "inner_key2" : "abc", "inner_key3": null }
            }
        ]$"#;
        let res: Result<Option<Peekable<CharIndices<'_>>>, String> = try_parse_array(json.char_indices().peekable());
        assert!(res.is_ok());
        let res = res.unwrap();
        assert!(res.is_some());
        assert_eq!(res.unwrap().peek(), Some(&(json.len() - 1,'$')));

        let json = r#"[1 "abc"]"#;
        let res: Result<Option<Peekable<CharIndices<'_>>>, String> = try_parse_array(json.char_indices().peekable());
        assert!(res.is_err());

        let json = r#"[1, 2"#;
        let res: Result<Option<Peekable<CharIndices<'_>>>, String> = try_parse_array(json.char_indices().peekable());
        assert!(res.is_err());
    } */
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProjectionRule {
    pub op: String,
    pub args: Vec<String>
}

impl FromStr for ProjectionRule {
    type Err = ZError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if let Some((op, args_string)) = s.split_once(',') {
            Ok(ProjectionRule {
                op: op.to_string(),
                args: args_string.split(',').map(String::from).collect()
            })
        } else if !s.is_empty() {
            Ok(ProjectionRule{
                op: s.to_string(),
                args: vec![]
            })
        } else {
            bail!(
                r#"Invalid ProjectionRule (must contain at least operation id)"): {}"#,
                s
            )
        }
    }
}

#[test]
fn test_parse_projection_rule() {
    assert_eq!(
        "slice".parse::<ProjectionRule>().unwrap(),
        ProjectionRule {
            op: "slice".to_string(),
            args: vec![]
        }
    );
    assert_eq!(
        "pick,a,b,c.x,c.y.z".parse::<ProjectionRule>().unwrap(),
        ProjectionRule {
            op: "pick".to_string(),
            args: vec![String::from("a"), String::from("b"), String::from("c.x"), String::from("c.y.z")]
        }
    );
    assert!("".parse::<ProjectionRule>().is_err());
}

pub struct FieldNamesTree<'a> {
    pub children: Option<Box<HashMap<&'a str, FieldNamesTree<'a>>>>
}

impl<'a> FieldNamesTree<'a> {
    pub fn new(initialize: bool) -> FieldNamesTree<'a> {
        FieldNamesTree {
            children: if initialize { Some(Box::new(HashMap::new())) } else { None }
        }
    }

    pub fn insert(&mut self, full_field_name_parts: &[Vec<&'a str>]) {
        if full_field_name_parts.is_empty() {
            return;
        }
        if full_field_name_parts[0].is_empty() {
            // ignore empty string fields
            self.insert(&full_field_name_parts[1..]);
        }
        if self.children.is_none() {
            self.children = Some(Box::new(HashMap::new()));
        }
        let children = self.children.as_mut().unwrap();
        for f in full_field_name_parts[0].as_slice() {
            let v = children
                .entry(f)
                .or_insert(Self::new(false));
            v.insert(&full_field_name_parts[1..])
        }
    }


    pub fn project_json(&self, json: &mut serde_json::Value) -> bool {
        let mut fields_found = false;
        if self.children.is_none() {
            return true;
        }
        let mut non_existing_fields = HashSet::<&str>::new();
        let children = self.children.as_ref().unwrap();
        if let Some(js_obj) = json.as_object_mut() {
            for (js_key, js_value) in js_obj.into_iter() {
                if let Some((k, c)) = children.get_key_value(js_key.as_str()) {
                    let inner_fields_found = c.project_json(js_value);
                    if !inner_fields_found {
                        non_existing_fields.insert(k);
                    }
                    fields_found = fields_found || inner_fields_found;
                }
            }
            js_obj.retain(|key, _| {
                children.contains_key(key.as_str()) && !non_existing_fields.contains(key.as_str())
            });
        } else if let Some(js_ar) = json.as_array_mut() {
            for v in js_ar.as_mut_slice() {
                let inner_fields_found = self.project_json(v);
                fields_found = fields_found || inner_fields_found;
            }
        }
        return fields_found;
    }

    pub fn get_subtree(&self, full_field_name_parts: &[&str]) -> Option<&'a FieldNamesTree> {
        if full_field_name_parts.is_empty() {
            Some(self)
        } else if self.is_empty() || self.children.as_ref().unwrap().is_empty() {
            None
        } else if let Some(v) = self.children.as_ref().unwrap().get(full_field_name_parts[0]) {
            v.get_subtree(&full_field_name_parts[1..])
        } else {
            None
        }
    }

    pub fn is_empty(&self) -> bool {
        self.children.is_none()
    }
}

#[test]
fn test_field_names_tree() {
    let mut t = FieldNamesTree::new(false);
    assert!(t.get_subtree(&["a", "b"]).is_none());
    assert!(t.get_subtree(&[]).is_some());
    t.insert(&[vec!["a"], vec!["b"]]);
    assert!(t.get_subtree(&["a", "b"]).is_some());
    assert!(t.get_subtree(&["a", "c"]).is_none());
    assert!(t.get_subtree(&["b", "a"]).is_none());
    t.insert(&[vec!["c"], vec!["d"], vec!["e", "f"]]);
    assert!(t.get_subtree(&["c", "d", "e"]).is_some());
    assert!(t.get_subtree(&["c", "d", "f"]).is_some());
    assert!(t.get_subtree(&["c", "d", "g"]).is_none());
}

#[test]
fn test_field_names_tree_project_json() {
    use serde_json::json;
    let mut t = FieldNamesTree::new(true);
    let js = json!({
        "data": "data",
        "nested": {
            "a": 1,
            "b": 2,
            "c": {
                "d": [
                    {
                        "int": 1,
                        "str": "abc"
                    },
                    {
                        "int": 2,
                        "str": "cde"
                    },
                      {
                        "int": 3,
                        "str": "fgh"
                      }
                ],
                "e" : true,
                "f" : "text"
            }
        }
    });

    let mut js2 = js.clone();
    t.project_json(&mut js2);
    let js2_expected = json!({});
    assert_eq!(js2, js2_expected);

    t.insert(&[vec!["data"]]);
    let mut js2 = js.clone();
    t.project_json(&mut js2);
    let js2_expected = json!({"data": "data"});
    assert_eq!(js2, js2_expected);

    t.insert(&[vec!["nested"], vec!["a", "b"]]);
    let mut js2 = js.clone();
    t.project_json(&mut js2);
    let js2_expected = json!({
        "data": "data",
        "nested": {
            "a": 1,
            "b": 2
        }
    });
    assert_eq!(js2, js2_expected);

    t.insert(&[vec!["nested"], vec!["c"], vec!["d"], vec!["int"]]);
    let mut js2 = js.clone();
    t.project_json(&mut js2);
    let js2_expected = json!({
        "data": "data",
        "nested": {
            "a": 1,
            "b": 2,
            "c": {
                "d": [
                    {
                        "int": 1,
                    },
                    {
                        "int": 2,
                    },
                    {
                        "int": 3,
                    }
                ],
            }
        }
    });
    assert_eq!(js2, js2_expected);
}

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
use std::collections::{HashMap, HashSet};

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

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


pub struct JsonFieldsTree<'a> {
    pub children: Option<Box<HashMap<&'a str, JsonFieldsTree<'a>>>>
}

impl<'a> JsonFieldsTree<'a> {
    pub fn new() -> JsonFieldsTree<'a> {
        JsonFieldsTree {
            children: None
        }
    }

    pub fn insert(&mut self, full_field_name_parts: &[&'a str]) {
        if full_field_name_parts.is_empty() {
            return;
        }
        if self.children.is_none() {
            self.children = Some(Box::new(HashMap::new()));
        }
        let v = self.children.as_mut()
            .unwrap()
            .entry(full_field_name_parts[0])
            .or_insert(Self::new());
        v.insert(&full_field_name_parts[1..])
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
        }
        return fields_found;
    }

    pub fn is_empty(&self) -> bool {
        self.children.is_none()
    }
}

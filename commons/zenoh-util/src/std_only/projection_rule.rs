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

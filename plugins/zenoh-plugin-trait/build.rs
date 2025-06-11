use std::{env, fs, path::Path};
// Copyright (c) 2025 ZettaScale Technology
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
fn main() {
    let cargo_lock_path = project_root::get_project_root().unwrap().join("cargo.lock");
    let cargo_lock = fs::read_to_string(cargo_lock_path.clone()).unwrap();
    let cargo_lock = cargo_lock.replace(r#"""#, r#"\""#);
    let out_dir = env::var_os("OUT_DIR").unwrap();
    let dest_path = Path::new(&out_dir).join("cargo_lock.rs");
    fs::write(
        &dest_path,
        format!(r#"const CARGO_LOCK: &str = "{}";"#, cargo_lock),
    )
    .unwrap();
    println!(
        "cargo:rerun-if-changed={}",
        cargo_lock_path.to_str().unwrap()
    );
}

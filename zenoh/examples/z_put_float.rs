//
// Copyright (c) 2017, 2020 ADLINK Technology Inc.
//
// This program and the accompanying materials are made available under the
// terms of the Eclipse Public License 2.0 which is available at
// http://www.eclipse.org/legal/epl-2.0, or the Apache License, Version 2.0
// which is available at https://www.apache.org/licenses/LICENSE-2.0.
//
// SPDX-License-Identifier: EPL-2.0 OR Apache-2.0
//
// Contributors:
//   ADLINK zenoh team, <zenoh@adlink-labs.tech>
//
use clap::{App, Arg};
use zenoh::config::Config;

#[async_std::main]
async fn main() {
    // initiate logging
    env_logger::init();

    let (config, path, value) = parse_args();

    println!("Open session");
    let session = zenoh::open(config).await.unwrap();

    println!("Put Float ('{}': '{}')", path, value);
    session.put(&path, value).await.unwrap();

    session.close().await.unwrap();
}

//
// Argument parsing -- look at the main for the zenoh-related code
//
fn parse_args() -> (Config, String, f64) {
    let default_value = std::f64::consts::PI.to_string();

    let args = App::new("zenoh put float example")
        .arg(
            Arg::from_usage("-m, --mode=[MODE] 'The zenoh session mode (peer by default).")
                .possible_values(&["peer", "client"]),
        )
        .arg(Arg::from_usage(
            "-e, --peer=[LOCATOR]...  'Peer locators used to initiate the zenoh session.'",
        ))
        .arg(Arg::from_usage(
            "-l, --listener=[LOCATOR]...   'Locators to listen on.'",
        ))
        .arg(Arg::from_usage(
            "-c, --config=[FILE]      'A configuration file.'",
        ))
        .arg(
            Arg::from_usage("-p, --path=[PATH]        'The name of the resource to put.'")
                .default_value("/demo/example/zenoh-rs-put"),
        )
        .arg(
            Arg::from_usage("-v, --value=[VALUE]      'The float value of the resource to put.'")
                .default_value(&default_value),
        )
        .arg(Arg::from_usage(
            "--no-multicast-scouting 'Disable the multicast-based scouting mechanism.'",
        ))
        .get_matches();

    let mut config = if let Some(conf_file) = args.value_of("config") {
        Config::from_file(conf_file).unwrap()
    } else {
        Config::default()
    };
    if let Some(Ok(mode)) = args.value_of("mode").map(|mode| mode.parse()) {
        config.set_mode(Some(mode)).unwrap();
    }
    match args.value_of("mode").map(|m| m.parse()) {
        Some(Ok(mode)) => {
            config.set_mode(Some(mode)).unwrap();
        }
        Some(Err(())) => panic!("Invalid mode"),
        None => {}
    };
    if let Some(values) = args.values_of("peer") {
        config.peers.extend(values.map(|v| v.parse().unwrap()))
    }
    if let Some(values) = args.values_of("listeners") {
        config.listeners.extend(values.map(|v| v.parse().unwrap()))
    }
    if args.is_present("no-multicast-scouting") {
        config.scouting.multicast.set_enabled(Some(false)).unwrap();
    }

    let path = args.value_of("path").unwrap().to_string();
    let value: f64 = args.value_of("value").unwrap().parse().unwrap();

    (config, path, value)
}

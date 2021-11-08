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
use futures::prelude::*;
use zenoh::config::Config;
use zenoh::prelude::*;
use zenoh::publisher::CongestionControl;
use zenoh::queryable::EVAL;

const HTML: &str = r#"
<div id="result"></div>
<script>
if(typeof(EventSource) !== "undefined") {
  var source = new EventSource("/demo/sse/event");
  source.addEventListener("PUT", function(e) {
    document.getElementById("result").innerHTML += e.data + "<br>";
  }, false);
} else {
  document.getElementById("result").innerHTML = "Sorry, your browser does not support server-sent events...";
}
</script>"#;

#[async_std::main]
async fn main() {
    // initiate logging
    env_logger::init();

    let config = parse_args();
    let key = "/demo/sse";
    let value = "Pub from sse server!";

    println!("Open session");
    let session = zenoh::open(config).await.unwrap();

    println!("Register Queryable on {}", key);
    let mut queryable = session.register_queryable(key).kind(EVAL).await.unwrap();

    async_std::task::spawn(
        queryable
            .receiver()
            .clone()
            .for_each(move |request| async move {
                request
                    .reply_async(Sample::new(key.to_string(), HTML))
                    .await;
            }),
    );

    let event_key = [key, "/event"].concat();

    print!("Register Resource {}", event_key);
    let rid = session.register_resource(&event_key).await.unwrap();
    println!(" => RId {}", rid);

    println!("Register Publisher on {}", rid);
    let _publ = session.publishing(rid).await.unwrap();

    println!("Put Data periodically ('{}': '{}')...", rid, value);

    println!(
        "Data updates are accessible through HTML5 SSE at http://<hostname>:8000{}",
        key
    );
    loop {
        session
            .put(rid, value)
            .encoding(Encoding::TEXT_PLAIN)
            .congestion_control(CongestionControl::Block)
            .await
            .unwrap();
        async_std::task::sleep(std::time::Duration::new(1, 0)).await;
    }
}

fn parse_args() -> Config {
    let args = App::new("zenoh ssl server example")
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

    config
}

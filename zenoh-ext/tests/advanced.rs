//
// Copyright (c) 2024 ZettaScale Technology
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

use zenoh::sample::SampleKind;
use zenoh_config::{EndPoint, WhatAmI};
use zenoh_ext::{DataSubscriberBuilderExt, PublisherBuilderExt};

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn test_advanced_history() {
    use std::time::Duration;

    use zenoh::internal::ztimeout;

    const TIMEOUT: Duration = Duration::from_secs(60);
    const SLEEP: Duration = Duration::from_secs(1);
    const PEER1_ENDPOINT: &str = "tcp/localhost:47450";

    const ADVANCED_HISTORY_KEYEXPR: &str = "test/advanced/history";

    zenoh_util::init_log_from_env_or("error");

    let peer1 = {
        let mut c = zenoh::Config::default();
        c.listen
            .endpoints
            .set(vec![PEER1_ENDPOINT.parse::<EndPoint>().unwrap()])
            .unwrap();
        c.scouting.multicast.set_enabled(Some(false)).unwrap();
        let _ = c.set_mode(Some(WhatAmI::Peer));
        let s = ztimeout!(zenoh::open(c)).unwrap();
        tracing::info!("Peer (1) ZID: {}", s.zid());
        s
    };

    let publ = ztimeout!(peer1.declare_publisher(ADVANCED_HISTORY_KEYEXPR).history(3)).unwrap();
    ztimeout!(publ.put("1")).unwrap();
    ztimeout!(publ.put("2")).unwrap();
    ztimeout!(publ.put("3")).unwrap();
    ztimeout!(publ.put("4")).unwrap();

    tokio::time::sleep(SLEEP).await;

    let peer2 = {
        let mut c = zenoh::Config::default();
        c.connect
            .endpoints
            .set(vec![PEER1_ENDPOINT.parse::<EndPoint>().unwrap()])
            .unwrap();
        c.scouting.multicast.set_enabled(Some(false)).unwrap();
        let _ = c.set_mode(Some(WhatAmI::Peer));
        let s = ztimeout!(zenoh::open(c)).unwrap();
        tracing::info!("Peer (2) ZID: {}", s.zid());
        s
    };

    let sub = ztimeout!(peer2.declare_subscriber(ADVANCED_HISTORY_KEYEXPR).history()).unwrap();
    tokio::time::sleep(SLEEP).await;

    ztimeout!(publ.put("5")).unwrap();
    tokio::time::sleep(SLEEP).await;

    let sample = ztimeout!(sub.recv_async()).unwrap();
    assert_eq!(sample.kind(), SampleKind::Put);
    assert_eq!(sample.payload().try_to_string().unwrap().as_ref(), "2");

    let sample = ztimeout!(sub.recv_async()).unwrap();
    assert_eq!(sample.kind(), SampleKind::Put);
    assert_eq!(sample.payload().try_to_string().unwrap().as_ref(), "3");

    let sample = ztimeout!(sub.recv_async()).unwrap();
    assert_eq!(sample.kind(), SampleKind::Put);
    assert_eq!(sample.payload().try_to_string().unwrap().as_ref(), "4");

    let sample = ztimeout!(sub.recv_async()).unwrap();
    assert_eq!(sample.kind(), SampleKind::Put);
    assert_eq!(sample.payload().try_to_string().unwrap().as_ref(), "5");

    assert!(sub.try_recv().unwrap().is_none());

    publ.undeclare().await.unwrap();
    // sub.undeclare().await.unwrap();

    peer1.close().await.unwrap();
    peer2.close().await.unwrap();
}
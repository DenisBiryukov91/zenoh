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

use std::{collections::HashMap, str::FromStr, time::Duration};

use uhlc::{Timestamp, HLC, NTP64};
use zenoh::{key_expr::OwnedKeyExpr, sample::SampleKind};
use zenoh_backend_traits::config::ReplicaConfig;

use super::{Event, LogLatest};
use crate::replication::{
    classification::{Interval, IntervalIdx, SubInterval, SubIntervalIdx},
    digest::{Digest, Fingerprint},
    log::EventInsertion,
};

fn generate_timestamp_matching(
    log: &LogLatest,
    hlc: &HLC,
    interval: u32,
    sub_interval: u32,
    delta: u64,
) -> Timestamp {
    let duration_since_epoch = Duration::from_millis(
        (log.configuration.interval.as_millis() * interval as u128
            + (log.configuration.interval.as_millis() / log.configuration.sub_intervals as u128)
                * sub_interval as u128) as u64
            + delta,
    );

    Timestamp::new(NTP64::from(duration_since_epoch), *hlc.get_id())
}

#[test]
fn test_insert() {
    let hlc = HLC::default();
    let mut log = LogLatest::new(
        OwnedKeyExpr::from_str("replication/test/**").unwrap(),
        None,
        ReplicaConfig {
            interval: Duration::from_secs(10),
            sub_intervals: 2,
            hot: 1,
            warm: 5,
            propagation_delay: Duration::from_millis(250),
        },
    );

    let event_10_0_0 = Event::new(
        Some(OwnedKeyExpr::from_str("10/0/0").unwrap()),
        generate_timestamp_matching(&log, &hlc, 10, 0, 0),
        SampleKind::Put,
    );
    assert!(!log.bloom_filter_event.check(event_10_0_0.key_expr()));
    assert_eq!(
        EventInsertion::New(event_10_0_0.clone()),
        log.insert_event(Event::new(
            event_10_0_0.key_expr().clone(),
            *event_10_0_0.timestamp(),
            SampleKind::Put
        ))
    );
    assert!(log.bloom_filter_event.check(event_10_0_0.key_expr()));

    let event_10_0_0_new = Event::new(
        event_10_0_0.key_expr().clone(),
        generate_timestamp_matching(&log, &hlc, 10, 0, 1),
        SampleKind::Put,
    );
    assert_eq!(
        EventInsertion::ReplacedOlder(event_10_0_0.clone()),
        log.insert_event(Event::new(
            event_10_0_0_new.key_expr().clone(),
            *event_10_0_0_new.timestamp(),
            SampleKind::Put
        ))
    );

    // Try to insert the same event a second time -> NotInsertedAsOlder.
    assert_eq!(
        EventInsertion::NotInsertedAsOlder,
        log.insert_event(Event::new(
            event_10_0_0_new.key_expr().clone(),
            *event_10_0_0_new.timestamp(),
            SampleKind::Put
        ))
    );

    let expected_interval = Interval::from([(
        SubIntervalIdx(0),
        SubInterval::from([event_10_0_0_new.clone()]),
    )]);
    let interval_10 = log.intervals.get(&IntervalIdx(10)).unwrap();
    assert_eq!(&expected_interval, interval_10);
    assert_eq!(event_10_0_0_new.fingerprint(), interval_10.fingerprint());
}

#[test]
fn test_digest() {
    let hlc = HLC::default();
    let mut log = LogLatest::new(
        OwnedKeyExpr::from_str("replication/test/**").unwrap(),
        None,
        ReplicaConfig {
            interval: Duration::from_secs(10),
            sub_intervals: 5,
            hot: 1,
            warm: 5,
            propagation_delay: Duration::from_millis(250),
        },
    );

    let event_warm_5_1_0 = Event::new(
        Some(OwnedKeyExpr::from_str("5/1/0").unwrap()),
        generate_timestamp_matching(&log, &hlc, 5, 1, 0),
        SampleKind::Put,
    );
    assert_eq!(
        EventInsertion::New(event_warm_5_1_0.clone()),
        log.insert_event(Event::new(
            event_warm_5_1_0.key_expr().clone(),
            *event_warm_5_1_0.timestamp(),
            SampleKind::Put
        ))
    );
    let event_warm_6_2_0 = Event::new(
        Some(OwnedKeyExpr::from_str("6/2/0").unwrap()),
        generate_timestamp_matching(&log, &hlc, 6, 2, 0),
        SampleKind::Put,
    );
    assert_eq!(
        EventInsertion::New(event_warm_6_2_0.clone()),
        log.insert_event(Event::new(
            event_warm_6_2_0.key_expr().clone(),
            *event_warm_6_2_0.timestamp(),
            SampleKind::Put
        ))
    );
    let event_warm_6_2_1 = Event::new(
        Some(OwnedKeyExpr::from_str("6/2/1").unwrap()),
        generate_timestamp_matching(&log, &hlc, 6, 2, 1),
        SampleKind::Put,
    );
    assert_eq!(
        EventInsertion::New(event_warm_6_2_1.clone()),
        log.insert_event(Event::new(
            event_warm_6_2_1.key_expr().clone(),
            *event_warm_6_2_1.timestamp(),
            SampleKind::Put
        ))
    );

    let event_hot_10_4_1 = Event::new(
        Some(OwnedKeyExpr::from_str("10/4/1").unwrap()),
        generate_timestamp_matching(&log, &hlc, 10, 4, 1),
        SampleKind::Put,
    );
    assert_eq!(
        EventInsertion::New(event_hot_10_4_1.clone()),
        log.insert_event(Event::new(
            event_hot_10_4_1.key_expr().clone(),
            *event_hot_10_4_1.timestamp(),
            SampleKind::Put
        ))
    );

    // "Burning" interval that should not appear in the Digest.
    let event_burning_11_0_0 = Event::new(
        Some(OwnedKeyExpr::from_str("11/0/0").unwrap()),
        generate_timestamp_matching(&log, &hlc, 11, 0, 42),
        SampleKind::Put,
    );
    assert_eq!(
        EventInsertion::New(event_burning_11_0_0.clone()),
        log.insert_event(Event::new(
            event_burning_11_0_0.key_expr().clone(),
            *event_burning_11_0_0.timestamp(),
            SampleKind::Put
        ))
    );

    // 🧊 There are no Event in the cold era.

    // We set the upper bound when generating the Digest to 10, so:
    // - 10 <= hot <= 10
    // - 5 <= warm <= 9
    // - 4 <= cold
    let mut expected_digest = Digest {
        configuration_fingerprint: log.configuration.fingerprint(),
        cold_era_fingerprint: Fingerprint::default(),
        warm_era_fingerprints: HashMap::from([
            (IntervalIdx(5), event_warm_5_1_0.fingerprint()),
            (
                IntervalIdx(6),
                event_warm_6_2_0.fingerprint() ^ event_warm_6_2_1.fingerprint(),
            ),
        ]),
        hot_era_fingerprints: HashMap::from([(
            IntervalIdx(10),
            HashMap::from([(SubIntervalIdx(4), event_hot_10_4_1.fingerprint())]),
        )]),
    };
    assert_eq!(expected_digest, log.digest_from(IntervalIdx(10)));

    // 🧊 Let's add some Events in the cold era.
    let event_cold_0_0_0 = Event::new(
        Some(OwnedKeyExpr::from_str("0/0/0").unwrap()),
        generate_timestamp_matching(&log, &hlc, 0, 0, 0),
        SampleKind::Put,
    );
    assert_eq!(
        EventInsertion::New(event_cold_0_0_0.clone()),
        log.insert_event(Event::new(
            event_cold_0_0_0.key_expr().clone(),
            *event_cold_0_0_0.timestamp(),
            SampleKind::Put
        ))
    );
    let event_cold_1_0_0 = Event::new(
        Some(OwnedKeyExpr::from_str("1/0/0").unwrap()),
        generate_timestamp_matching(&log, &hlc, 1, 0, 0),
        SampleKind::Put,
    );
    assert_eq!(
        EventInsertion::New(event_cold_1_0_0.clone()),
        log.insert_event(Event::new(
            event_cold_1_0_0.key_expr().clone(),
            *event_cold_1_0_0.timestamp(),
            SampleKind::Put
        ))
    );
    let event_cold_2_0_0 = Event::new(
        Some(OwnedKeyExpr::from_str("2/0/0").unwrap()),
        generate_timestamp_matching(&log, &hlc, 2, 0, 0),
        SampleKind::Put,
    );
    assert_eq!(
        EventInsertion::New(event_cold_2_0_0.clone()),
        log.insert_event(Event::new(
            event_cold_2_0_0.key_expr().clone(),
            *event_cold_2_0_0.timestamp(),
            SampleKind::Put
        ))
    );
    let event_cold_4_0_0 = Event::new(
        Some(OwnedKeyExpr::from_str("4/0/0").unwrap()),
        generate_timestamp_matching(&log, &hlc, 4, 0, 0),
        SampleKind::Put,
    );
    assert_eq!(
        EventInsertion::New(event_cold_4_0_0.clone()),
        log.insert_event(Event::new(
            event_cold_4_0_0.key_expr().clone(),
            *event_cold_4_0_0.timestamp(),
            SampleKind::Put
        ))
    );

    let expected_cold_fingerprint = event_cold_0_0_0.fingerprint()
        ^ event_cold_1_0_0.fingerprint()
        ^ event_cold_2_0_0.fingerprint()
        ^ event_cold_4_0_0.fingerprint();
    expected_digest.cold_era_fingerprint = expected_cold_fingerprint;
    assert_eq!(expected_digest, log.digest_from(IntervalIdx(10)));

    // We now set the upper bound when generating the Digest to 12, so:
    // - 12 <= hot <= 12
    // - 7 <= warm <= 11
    // - cold <= 6
    let expected_cold_fingerprint = event_cold_0_0_0.fingerprint()
        ^ event_cold_1_0_0.fingerprint()
        ^ event_cold_2_0_0.fingerprint()
        ^ event_cold_4_0_0.fingerprint()
        ^ event_warm_5_1_0.fingerprint()
        ^ event_warm_6_2_0.fingerprint()
        ^ event_warm_6_2_1.fingerprint();
    let expected_digest = Digest {
        configuration_fingerprint: log.configuration.fingerprint(),
        cold_era_fingerprint: expected_cold_fingerprint,
        warm_era_fingerprints: HashMap::from([
            (IntervalIdx(10), event_hot_10_4_1.fingerprint()),
            (IntervalIdx(11), event_burning_11_0_0.fingerprint()),
        ]),
        hot_era_fingerprints: HashMap::default(),
    };
    assert_eq!(expected_digest, log.digest_from(IntervalIdx(12)));
}

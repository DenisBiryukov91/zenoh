//
// Copyright (c) 2022 ZettaScale Technology
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
use std::{future::IntoFuture, str::FromStr};

use zenoh::{
    config::ZenohId,
    handlers::{Callback, IntoHandler},
    key_expr::KeyExpr,
    query::{ConsolidationMode, Selector},
    sample::{Locality, Sample, SampleKind},
    session::{EntityGlobalId, EntityId},
    Resolvable, Resolve, Session, Wait,
};
use zenoh_util::{Timed, TimedEvent, Timer};
#[zenoh_macros::unstable]
use {
    async_trait::async_trait,
    std::collections::hash_map::Entry,
    std::collections::HashMap,
    std::convert::TryFrom,
    std::future::Ready,
    std::sync::{Arc, Mutex},
    std::time::Duration,
    uhlc::ID,
    zenoh::handlers::{locked, DefaultHandler},
    zenoh::internal::zlock,
    zenoh::pubsub::Subscriber,
    zenoh::query::{QueryTarget, Reply, ReplyKeyExpr},
    zenoh::time::Timestamp,
    zenoh::Result as ZResult,
};

use crate::advanced_cache::{ke_liveliness, KE_PREFIX, KE_STAR, KE_UHLC};

#[derive(Debug, Default, Clone)]
/// Configure query for historical data.
pub struct HistoryConfig {
    liveliness: bool,
    // sample_depth: usize,
}

impl HistoryConfig {
    /// Enable detection of late joiner publishers and query for their historical data.
    ///
    /// Let joiner detection can only be achieved for Publishers that enable late_joiner_detection.
    /// History can only be retransmitted by Publishers that enable caching.
    #[zenoh_macros::unstable]
    #[inline]
    pub fn late_joiner(mut self) -> Self {
        self.liveliness = true;
        self
    }

    // /// Specify how many samples to keep for each resource.
    // pub fn max_samples(mut self, depth: usize) -> Self {
    //     self.sample_depth = depth;
    //     self
    // }

    // TODO pub fn max_age(mut self, depth: Duration) -> Self
}

#[derive(Default)]
/// Configure retransmission.
pub struct RecoveryConfig {
    periodic_queries: Option<Duration>,
}

impl std::fmt::Debug for RecoveryConfig {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut s = f.debug_struct("RetransmissionConf");
        s.field("periodic_queries", &self.periodic_queries);
        s.finish()
    }
}

impl RecoveryConfig {
    /// Enable periodic queries for not yet received Samples and specify their period.
    ///
    /// This allows to retrieve the last Sample(s) if the last Sample(s) is/are lost.
    /// So it is useful for sporadic publications but useless for periodic publications
    /// with a period smaller or equal to this period.
    /// Retransmission can only be achieved by Publishers that also activate retransmission.
    #[zenoh_macros::unstable]
    #[inline]
    pub fn periodic_queries(mut self, period: Option<Duration>) -> Self {
        self.periodic_queries = period;
        self
    }
}

/// The builder of AdvancedSubscriber, allowing to configure it.
#[zenoh_macros::unstable]
pub struct AdvancedSubscriberBuilder<'a, 'b, Handler, const BACKGROUND: bool = false> {
    pub(crate) session: &'a Session,
    pub(crate) key_expr: ZResult<KeyExpr<'b>>,
    pub(crate) origin: Locality,
    pub(crate) sample_miss_callback: Option<Arc<dyn Fn(EntityGlobalId, u32) + Send + Sync>>,
    pub(crate) retransmission: Option<RecoveryConfig>,
    pub(crate) query_target: QueryTarget,
    pub(crate) query_timeout: Duration,
    pub(crate) history: Option<HistoryConfig>,
    pub(crate) handler: Handler,
}

#[zenoh_macros::unstable]
impl<'a, 'b, Handler> AdvancedSubscriberBuilder<'a, 'b, Handler> {
    pub(crate) fn new(
        session: &'a Session,
        key_expr: ZResult<KeyExpr<'b>>,
        origin: Locality,
        handler: Handler,
    ) -> Self {
        AdvancedSubscriberBuilder {
            session,
            key_expr,
            origin,
            handler,
            sample_miss_callback: None,
            retransmission: None,
            query_target: QueryTarget::All,
            query_timeout: Duration::from_secs(10),
            history: None,
        }
    }
}

#[zenoh_macros::unstable]
impl<'a, 'b> AdvancedSubscriberBuilder<'a, 'b, DefaultHandler> {
    /// Add callback to AdvancedSubscriber.
    #[inline]
    pub fn callback<Callback>(
        self,
        callback: Callback,
    ) -> AdvancedSubscriberBuilder<'a, 'b, Callback>
    where
        Callback: Fn(Sample) + Send + Sync + 'static,
    {
        AdvancedSubscriberBuilder {
            session: self.session,
            key_expr: self.key_expr.map(|s| s.into_owned()),
            origin: self.origin,
            sample_miss_callback: self.sample_miss_callback,
            retransmission: self.retransmission,
            query_target: self.query_target,
            query_timeout: self.query_timeout,
            history: self.history,
            handler: callback,
        }
    }

    /// Add callback to `AdvancedSubscriber`.
    ///
    /// Using this guarantees that your callback will never be called concurrently.
    /// If your callback is also accepted by the [`callback`](AdvancedSubscriberBuilder::callback) method, we suggest you use it instead of `callback_mut`
    #[inline]
    pub fn callback_mut<CallbackMut>(
        self,
        callback: CallbackMut,
    ) -> AdvancedSubscriberBuilder<'a, 'b, impl Fn(Sample) + Send + Sync + 'static>
    where
        CallbackMut: FnMut(Sample) + Send + Sync + 'static,
    {
        self.callback(locked(callback))
    }

    /// Make the built AdvancedSubscriber an [`AdvancedSubscriber`](AdvancedSubscriber).
    #[inline]
    pub fn with<Handler>(self, handler: Handler) -> AdvancedSubscriberBuilder<'a, 'b, Handler>
    where
        Handler: IntoHandler<Sample>,
    {
        AdvancedSubscriberBuilder {
            session: self.session,
            key_expr: self.key_expr.map(|s| s.into_owned()),
            origin: self.origin,
            sample_miss_callback: self.sample_miss_callback,
            retransmission: self.retransmission,
            query_target: self.query_target,
            query_timeout: self.query_timeout,
            history: self.history,
            handler,
        }
    }
}

#[zenoh_macros::unstable]
impl<'a, 'b, Handler> AdvancedSubscriberBuilder<'a, 'b, Handler> {
    /// Restrict the matching publications that will be receive by this [`Subscriber`]
    /// to the ones that have the given [`Locality`](crate::prelude::Locality).
    #[zenoh_macros::unstable]
    #[inline]
    pub fn allowed_origin(mut self, origin: Locality) -> Self {
        self.origin = origin;
        self
    }

    #[zenoh_macros::unstable]
    #[inline]
    pub fn sample_miss_callback(
        mut self,
        callback: impl Fn(EntityGlobalId, u32) + Send + Sync + 'static,
    ) -> Self {
        self.sample_miss_callback = Some(Arc::new(callback));
        self
    }

    /// Ask for retransmission of detected lost Samples.
    ///
    /// Retransmission can only be achieved by Publishers that enable
    /// caching and sample_miss_detection.
    #[zenoh_macros::unstable]
    #[inline]
    pub fn recovery(mut self, conf: RecoveryConfig) -> Self {
        self.retransmission = Some(conf);
        self
    }

    // /// Change the target to be used for queries.

    // #[inline]
    // pub fn query_target(mut self, query_target: QueryTarget) -> Self {
    //     self.query_target = query_target;
    //     self
    // }

    /// Change the timeout to be used for queries (history, retransmission).
    #[zenoh_macros::unstable]
    #[inline]
    pub fn query_timeout(mut self, query_timeout: Duration) -> Self {
        self.query_timeout = query_timeout;
        self
    }

    /// Enable query for historical data.
    ///
    /// History can only be retransmitted by Publishers that enable caching.
    #[zenoh_macros::unstable]
    #[inline]
    pub fn history(mut self, config: HistoryConfig) -> Self {
        self.history = Some(config);
        self
    }

    fn with_static_keys(self) -> AdvancedSubscriberBuilder<'a, 'static, Handler> {
        AdvancedSubscriberBuilder {
            session: self.session,
            key_expr: self.key_expr.map(|s| s.into_owned()),
            origin: self.origin,
            sample_miss_callback: self.sample_miss_callback,
            retransmission: self.retransmission,
            query_target: self.query_target,
            query_timeout: self.query_timeout,
            history: self.history,
            handler: self.handler,
        }
    }
}

impl<Handler> Resolvable for AdvancedSubscriberBuilder<'_, '_, Handler>
where
    Handler: IntoHandler<Sample>,
    Handler::Handler: Send,
{
    type To = ZResult<AdvancedSubscriber<Handler::Handler>>;
}

impl<Handler> Wait for AdvancedSubscriberBuilder<'_, '_, Handler>
where
    Handler: IntoHandler<Sample> + Send,
    Handler::Handler: Send,
{
    fn wait(self) -> <Self as Resolvable>::To {
        AdvancedSubscriber::new(self.with_static_keys())
    }
}

impl<Handler> IntoFuture for AdvancedSubscriberBuilder<'_, '_, Handler>
where
    Handler: IntoHandler<Sample> + Send,
    Handler::Handler: Send,
{
    type Output = <Self as Resolvable>::To;
    type IntoFuture = Ready<<Self as Resolvable>::To>;

    fn into_future(self) -> Self::IntoFuture {
        std::future::ready(self.wait())
    }
}

struct Period {
    timer: Timer,
    period: Duration,
}

#[zenoh_macros::unstable]
struct State {
    global_pending_queries: u64,
    sequenced_states: HashMap<EntityGlobalId, SourceState<u32>>,
    timestamped_states: HashMap<ID, SourceState<Timestamp>>,
    session: Session,
    key_expr: KeyExpr<'static>,
    retransmission: bool,
    period: Option<Period>,
    query_target: QueryTarget,
    query_timeout: Duration,
    callback: Callback<Sample>,
    miss_callback: Option<Arc<dyn Fn(EntityGlobalId, u32) + Send + Sync>>,
}

macro_rules! spawn_periodoic_queries {
    ($p:expr,$s:expr,$r:expr) => {{
        if let Some(period) = &$p.period {
            period.timer.add(TimedEvent::periodic(
                period.period,
                PeriodicQuery {
                    source_id: $s,
                    statesref: $r,
                },
            ))
        }
    }};
}

#[zenoh_macros::unstable]
struct SourceState<T> {
    last_delivered: Option<T>,
    pending_queries: u64,
    pending_samples: HashMap<T, Sample>,
}

#[zenoh_macros::unstable]
pub struct AdvancedSubscriber<Receiver> {
    _subscriber: Subscriber<()>,
    receiver: Receiver,
    _liveliness_subscriber: Option<Subscriber<()>>,
}

#[zenoh_macros::unstable]
impl<Receiver> std::ops::Deref for AdvancedSubscriber<Receiver> {
    type Target = Receiver;
    fn deref(&self) -> &Self::Target {
        &self.receiver
    }
}

#[zenoh_macros::unstable]
impl<Receiver> std::ops::DerefMut for AdvancedSubscriber<Receiver> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.receiver
    }
}

#[zenoh_macros::unstable]
fn handle_sample(states: &mut State, sample: Sample) -> bool {
    if let (Some(source_id), Some(source_sn)) = (
        sample.source_info().source_id(),
        sample.source_info().source_sn(),
    ) {
        let entry = states.sequenced_states.entry(*source_id);
        let new = matches!(&entry, Entry::Vacant(_));
        let state = entry.or_insert(SourceState::<u32> {
            last_delivered: None,
            pending_queries: 0,
            pending_samples: HashMap::new(),
        });
        if states.global_pending_queries != 0 {
            state.pending_samples.insert(source_sn, sample);
        } else if state.last_delivered.is_some() && source_sn != state.last_delivered.unwrap() + 1 {
            if source_sn > state.last_delivered.unwrap() {
                if states.retransmission {
                    state.pending_samples.insert(source_sn, sample);
                } else {
                    tracing::info!(
                        "Sample missed: missed {} samples from {:?}.",
                        source_sn - state.last_delivered.unwrap() - 1,
                        source_id,
                    );
                    if let Some(miss_callback) = states.miss_callback.as_ref() {
                        (miss_callback)(*source_id, source_sn - state.last_delivered.unwrap() - 1);
                        states.callback.call(sample);
                        state.last_delivered = Some(source_sn);
                    }
                }
            }
        } else {
            states.callback.call(sample);
            let mut last_seq_num = source_sn;
            state.last_delivered = Some(last_seq_num);
            while let Some(s) = state.pending_samples.remove(&(last_seq_num + 1)) {
                states.callback.call(s);
                last_seq_num += 1;
                state.last_delivered = Some(last_seq_num);
            }
        }
        new
    } else if let Some(timestamp) = sample.timestamp() {
        let entry = states.timestamped_states.entry(*timestamp.get_id());
        let state = entry.or_insert(SourceState::<Timestamp> {
            last_delivered: None,
            pending_queries: 0,
            pending_samples: HashMap::new(),
        });
        if state.last_delivered.map(|t| t < *timestamp).unwrap_or(true) {
            if states.global_pending_queries == 0 && state.pending_queries == 0 {
                state.last_delivered = Some(*timestamp);
                states.callback.call(sample);
            } else {
                state.pending_samples.entry(*timestamp).or_insert(sample);
            }
        }
        false
    } else {
        states.callback.call(sample);
        false
    }
}

#[zenoh_macros::unstable]
fn seq_num_range(start: Option<u32>, end: Option<u32>) -> String {
    match (start, end) {
        (Some(start), Some(end)) => format!("_sn={}..{}", start, end),
        (Some(start), None) => format!("_sn={}..", start),
        (None, Some(end)) => format!("_sn=..{}", end),
        (None, None) => "_sn=..".to_string(),
    }
}

#[zenoh_macros::unstable]
#[derive(Clone)]
struct PeriodicQuery {
    source_id: EntityGlobalId,
    statesref: Arc<Mutex<State>>,
}

#[zenoh_macros::unstable]
#[async_trait]
impl Timed for PeriodicQuery {
    async fn run(&mut self) {
        let mut lock = zlock!(self.statesref);
        let states = &mut *lock;
        if let Some(state) = states.sequenced_states.get_mut(&self.source_id) {
            state.pending_queries += 1;
            let query_expr = KE_PREFIX
                / &self.source_id.zid().into_keyexpr()
                / &KeyExpr::try_from(self.source_id.eid().to_string()).unwrap()
                / &states.key_expr;
            let seq_num_range = seq_num_range(Some(state.last_delivered.unwrap() + 1), None);

            let session = states.session.clone();
            let key_expr = states.key_expr.clone().into_owned();
            let query_target = states.query_target;
            let query_timeout = states.query_timeout;
            drop(lock);
            let handler = SequencedRepliesHandler {
                source_id: self.source_id,
                statesref: self.statesref.clone(),
            };
            let _ = session
                .get(Selector::from((query_expr, seq_num_range)))
                .callback({
                    move |r: Reply| {
                        if let Ok(s) = r.into_result() {
                            if key_expr.intersects(s.key_expr()) {
                                let states = &mut *zlock!(handler.statesref);
                                handle_sample(states, s);
                            }
                        }
                    }
                })
                .consolidation(ConsolidationMode::None)
                .accept_replies(ReplyKeyExpr::Any)
                .target(query_target)
                .timeout(query_timeout)
                .wait();
        }
    }
}

#[zenoh_macros::unstable]
impl<Handler> AdvancedSubscriber<Handler> {
    fn new<H>(conf: AdvancedSubscriberBuilder<'_, '_, H>) -> ZResult<Self>
    where
        H: IntoHandler<Sample, Handler = Handler> + Send,
    {
        let (callback, receiver) = conf.handler.into_handler();
        let key_expr = conf.key_expr?;
        let retransmission = conf.retransmission;
        let query_target = conf.query_target;
        let query_timeout = conf.query_timeout;
        let session = conf.session.clone();
        let statesref = Arc::new(Mutex::new(State {
            sequenced_states: HashMap::new(),
            timestamped_states: HashMap::new(),
            global_pending_queries: if conf.history.is_some() { 1 } else { 0 },
            session,
            period: retransmission.as_ref().and_then(|r| {
                r.periodic_queries.map(|p| Period {
                    timer: Timer::new(false),
                    period: p,
                })
            }),
            key_expr: key_expr.clone().into_owned(),
            retransmission: retransmission.is_some(),
            query_target: conf.query_target,
            query_timeout: conf.query_timeout,
            callback: callback.clone(),
            miss_callback: conf.sample_miss_callback,
        }));

        let sub_callback = {
            let statesref = statesref.clone();
            let session = conf.session.clone();
            let key_expr = key_expr.clone().into_owned();

            move |s: Sample| {
                let mut lock = zlock!(statesref);
                let states = &mut *lock;
                let source_id = s.source_info().source_id().cloned();
                let new = handle_sample(states, s);

                if let Some(source_id) = source_id {
                    if new {
                        spawn_periodoic_queries!(states, source_id, statesref.clone());
                    }

                    if let Some(state) = states.sequenced_states.get_mut(&source_id) {
                        if retransmission.is_some()
                            && state.pending_queries == 0
                            && !state.pending_samples.is_empty()
                        {
                            state.pending_queries += 1;
                            let query_expr = KE_PREFIX
                                / &source_id.zid().into_keyexpr()
                                / &KeyExpr::try_from(source_id.eid().to_string()).unwrap()
                                / &key_expr;
                            let seq_num_range =
                                seq_num_range(Some(state.last_delivered.unwrap() + 1), None);
                            drop(lock);
                            let handler = SequencedRepliesHandler {
                                source_id,
                                statesref: statesref.clone(),
                            };
                            let _ = session
                                .get(Selector::from((query_expr, seq_num_range)))
                                .callback({
                                    let key_expr = key_expr.clone().into_owned();
                                    move |r: Reply| {
                                        if let Ok(s) = r.into_result() {
                                            if key_expr.intersects(s.key_expr()) {
                                                let states = &mut *zlock!(handler.statesref);
                                                handle_sample(states, s);
                                            }
                                        }
                                    }
                                })
                                .consolidation(ConsolidationMode::None)
                                .accept_replies(ReplyKeyExpr::Any)
                                .target(query_target)
                                .timeout(query_timeout)
                                .wait();
                        }
                    }
                }
            }
        };

        let subscriber = conf
            .session
            .declare_subscriber(&key_expr)
            .callback(sub_callback)
            .allowed_origin(conf.origin)
            .wait()?;

        if conf.history.is_some() {
            let handler = InitialRepliesHandler {
                statesref: statesref.clone(),
            };
            let _ = conf
                .session
                .get(Selector::from((
                    KE_PREFIX / KE_STAR / KE_STAR / &key_expr,
                    "0..",
                )))
                .callback({
                    let key_expr = key_expr.clone().into_owned();
                    move |r: Reply| {
                        if let Ok(s) = r.into_result() {
                            if key_expr.intersects(s.key_expr()) {
                                let states = &mut *zlock!(handler.statesref);
                                handle_sample(states, s);
                            }
                        }
                    }
                })
                .consolidation(ConsolidationMode::None)
                .accept_replies(ReplyKeyExpr::Any)
                .target(query_target)
                .timeout(query_timeout)
                .wait();
        }

        let liveliness_subscriber = if conf.history.is_some_and(|h| h.liveliness) {
            let live_callback = {
                let session = conf.session.clone();
                let statesref = statesref.clone();
                let key_expr = key_expr.clone().into_owned();
                move |s: Sample| {
                    if s.kind() == SampleKind::Put {
                        if let Ok(parsed) = ke_liveliness::parse(s.key_expr().as_keyexpr()) {
                            if let Ok(zid) = ZenohId::from_str(parsed.zid().as_str()) {
                                // TODO : If we already have a state associated to this discovered source
                                // we should query with the appropriate range to avoid unnecessary retransmissions
                                if parsed.eid() == KE_UHLC {
                                    let states = &mut *zlock!(statesref);
                                    let entry = states.timestamped_states.entry(ID::from(zid));
                                    let state = entry.or_insert(SourceState::<Timestamp> {
                                        last_delivered: None,
                                        pending_queries: 0,
                                        pending_samples: HashMap::new(),
                                    });
                                    state.pending_queries += 1;

                                    let handler = TimestampedRepliesHandler {
                                        id: ID::from(zid),
                                        statesref: statesref.clone(),
                                        callback: callback.clone(),
                                    };
                                    let _ = session
                                        .get(Selector::from((s.key_expr(), "0..")))
                                        .callback({
                                            let key_expr = key_expr.clone().into_owned();
                                            move |r: Reply| {
                                                if let Ok(s) = r.into_result() {
                                                    if key_expr.intersects(s.key_expr()) {
                                                        let states =
                                                            &mut *zlock!(handler.statesref);
                                                        handle_sample(states, s);
                                                    }
                                                }
                                            }
                                        })
                                        .consolidation(ConsolidationMode::None)
                                        .accept_replies(ReplyKeyExpr::Any)
                                        .target(query_target)
                                        .timeout(query_timeout)
                                        .wait();
                                } else if let Ok(eid) = EntityId::from_str(parsed.eid().as_str()) {
                                    let source_id = EntityGlobalId::new(zid, eid);
                                    let states = &mut *zlock!(statesref);
                                    let entry = states.sequenced_states.entry(source_id);
                                    let new = matches!(&entry, Entry::Vacant(_));
                                    let state = entry.or_insert(SourceState::<u32> {
                                        last_delivered: None,
                                        pending_queries: 0,
                                        pending_samples: HashMap::new(),
                                    });
                                    state.pending_queries += 1;

                                    let handler = SequencedRepliesHandler {
                                        source_id,
                                        statesref: statesref.clone(),
                                    };
                                    let _ = session
                                        .get(Selector::from((s.key_expr(), "0..")))
                                        .callback({
                                            let key_expr = key_expr.clone().into_owned();
                                            move |r: Reply| {
                                                if let Ok(s) = r.into_result() {
                                                    if key_expr.intersects(s.key_expr()) {
                                                        let states =
                                                            &mut *zlock!(handler.statesref);
                                                        handle_sample(states, s);
                                                    }
                                                }
                                            }
                                        })
                                        .consolidation(ConsolidationMode::None)
                                        .accept_replies(ReplyKeyExpr::Any)
                                        .target(query_target)
                                        .timeout(query_timeout)
                                        .wait();

                                    if new {
                                        spawn_periodoic_queries!(
                                            states,
                                            source_id,
                                            statesref.clone()
                                        );
                                    }
                                }
                            } else {
                                let states = &mut *zlock!(statesref);
                                states.global_pending_queries += 1;

                                let handler = InitialRepliesHandler {
                                    statesref: statesref.clone(),
                                };
                                let _ = session
                                    .get(Selector::from((s.key_expr(), "0..")))
                                    .callback({
                                        let key_expr = key_expr.clone().into_owned();
                                        move |r: Reply| {
                                            if let Ok(s) = r.into_result() {
                                                if key_expr.intersects(s.key_expr()) {
                                                    let states = &mut *zlock!(handler.statesref);
                                                    handle_sample(states, s);
                                                }
                                            }
                                        }
                                    })
                                    .consolidation(ConsolidationMode::None)
                                    .accept_replies(ReplyKeyExpr::Any)
                                    .target(query_target)
                                    .timeout(query_timeout)
                                    .wait();
                            }
                        } else {
                            tracing::warn!(
                                "Received malformed liveliness token key expression: {}",
                                s.key_expr()
                            );
                        }
                    }
                }
            };

            Some(
                conf
                .session
                .liveliness()
                .declare_subscriber(KE_PREFIX / KE_STAR / KE_STAR / &key_expr)
                // .declare_subscriber(keformat!(ke_liveliness_all::formatter(), zid = 0, eid = 0, remaining = key_expr).unwrap())
                .history(true)
                .callback(live_callback)
                .wait()?,
            )
        } else {
            None
        };

        let reliable_subscriber = AdvancedSubscriber {
            _subscriber: subscriber,
            receiver,
            _liveliness_subscriber: liveliness_subscriber,
        };

        Ok(reliable_subscriber)
    }

    /// Close this AdvancedSubscriber
    #[inline]
    pub fn close(self) -> impl Resolve<ZResult<()>> {
        self._subscriber.undeclare()
    }
}

#[zenoh_macros::unstable]
#[inline]
fn flush_sequenced_source(
    state: &mut SourceState<u32>,
    callback: &Callback<Sample>,
    source_id: &EntityGlobalId,
    miss_callback: Option<&Arc<dyn Fn(EntityGlobalId, u32) + Send + Sync>>,
) {
    if state.pending_queries == 0 && !state.pending_samples.is_empty() {
        let mut pending_samples = state
            .pending_samples
            .drain()
            .collect::<Vec<(u32, Sample)>>();
        pending_samples.sort_by_key(|(k, _s)| *k);
        for (seq_num, sample) in pending_samples {
            match state.last_delivered {
                None => {
                    state.last_delivered = Some(seq_num);
                    callback.call(sample);
                }
                Some(last) if seq_num == last + 1 => {
                    state.last_delivered = Some(seq_num);
                    callback.call(sample);
                }
                Some(last) if seq_num > last + 1 => {
                    tracing::warn!(
                        "Sample missed: missed {} samples from {:?}.",
                        seq_num - last - 1,
                        source_id,
                    );
                    if let Some(miss_callback) = miss_callback {
                        (miss_callback)(*source_id, seq_num - last - 1)
                    }
                    state.last_delivered = Some(seq_num);
                    callback.call(sample);
                }
                _ => {
                    // duplicate
                }
            }
        }
    }
}

#[zenoh_macros::unstable]
#[inline]
fn flush_timestamped_source(state: &mut SourceState<Timestamp>, callback: &Callback<Sample>) {
    if state.pending_queries == 0 && !state.pending_samples.is_empty() {
        let mut pending_samples = state
            .pending_samples
            .drain()
            .collect::<Vec<(Timestamp, Sample)>>();
        pending_samples.sort_by_key(|(k, _s)| *k);
        for (timestamp, sample) in pending_samples {
            if state
                .last_delivered
                .map(|last| timestamp > last)
                .unwrap_or(true)
            {
                state.last_delivered = Some(timestamp);
                callback.call(sample);
            }
        }
    }
}

#[zenoh_macros::unstable]
#[derive(Clone)]
struct InitialRepliesHandler {
    statesref: Arc<Mutex<State>>,
}

#[zenoh_macros::unstable]
impl Drop for InitialRepliesHandler {
    fn drop(&mut self) {
        let states = &mut *zlock!(self.statesref);
        states.global_pending_queries = states.global_pending_queries.saturating_sub(1);

        if states.global_pending_queries == 0 {
            for (source_id, state) in states.sequenced_states.iter_mut() {
                flush_sequenced_source(
                    state,
                    &states.callback,
                    source_id,
                    states.miss_callback.as_ref(),
                );
                spawn_periodoic_queries!(states, *source_id, self.statesref.clone());
            }
            for state in states.timestamped_states.values_mut() {
                flush_timestamped_source(state, &states.callback);
            }
        }
    }
}

#[zenoh_macros::unstable]
#[derive(Clone)]
struct SequencedRepliesHandler {
    source_id: EntityGlobalId,
    statesref: Arc<Mutex<State>>,
}

#[zenoh_macros::unstable]
impl Drop for SequencedRepliesHandler {
    fn drop(&mut self) {
        let states = &mut *zlock!(self.statesref);
        if let Some(state) = states.sequenced_states.get_mut(&self.source_id) {
            state.pending_queries = state.pending_queries.saturating_sub(1);
            if states.global_pending_queries == 0 {
                flush_sequenced_source(
                    state,
                    &states.callback,
                    &self.source_id,
                    states.miss_callback.as_ref(),
                )
            }
        }
    }
}

#[zenoh_macros::unstable]
#[derive(Clone)]
struct TimestampedRepliesHandler {
    id: ID,
    statesref: Arc<Mutex<State>>,
    callback: Callback<Sample>,
}

#[zenoh_macros::unstable]
impl Drop for TimestampedRepliesHandler {
    fn drop(&mut self) {
        let states = &mut *zlock!(self.statesref);
        if let Some(state) = states.timestamped_states.get_mut(&self.id) {
            state.pending_queries = state.pending_queries.saturating_sub(1);
            if states.global_pending_queries == 0 {
                flush_timestamped_source(state, &self.callback);
            }
        }
    }
}

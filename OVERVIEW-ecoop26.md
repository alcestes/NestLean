# NestLean — proof overview

This file describes the mechanisation strategy for `monitor_soundness`,
which is superseded by the coinductive monitor soundness result
`monitor_soundness_co` (see [OVERVIEW.md](OVERVIEW.md)), and maps each proof
ingredient to the `.lean` file, definition, or lemma that provides it. Files are listed in dependency order:
each layer only builds on the layers above it.

## 1. What is proved

**Theorem** `monitor_soundness` (`Nest/MonitorSoundness.lean`):
a network `N` that is well-formed, has no self-sends, has all roles present,
is deeply prunable (`Network.Prunable`), output-live (`IsOutputLiveNetwork`),
and half-duplex (`IsHalfDuplex`) is *internally bisimilar*
(`InternallyBisimilar`) to its consistent instrumentation `MN`
(`consistentInstrumentation N = some MN`). Monitorability
(`Network.Monitorable`) is not assumed: it is derived from prunability
(`Network.Monitorable.of_Prunable` via `prunable_implies_monitorable`)
and then preserved along runs.

The witness relation is
`R N' MN' := consistentInstrumentation N' = some MN' ∧ net_trans_star N N'`,
i.e. consistency plus `τ*`-reachability. The proof is a coinductive
bisimulation argument with four matching directions
(`τ_dequeue`/`τ_comm`, each side), closed under reachability by
preservation lemmas.

## 2. Proof strategy

1. **Dequeue steps match unconditionally.**
   `network_dequeue_mon_dequeue` and `mon_dequeue_network_dequeue`
   (`Nest/DequeueCorrespondence.lean`) move a `τ_dequeue` across the
   instrumentation in both directions. The hard part is absorption:
   `habs_full` shows dequeues preserve monitor-fold endpoints along
   `UnfoldStar` chains (via `absorb_transfer_headnormal`,
   `maxRecover_unfold`).
2. **Communication steps match conditionally on drainability.**
   `network_comm_mon_comm` / `mon_comm_network_comm`
   (`Nest/MonitorSoundness.lean`) move a `τ_comm` across, but each side
   needs a monitor fold to exist for the post-step configuration
   (via `monitor_fold_aux_out_aux_general` and `monitor_fold_aux_append_iff`).
3. **Missing folds are impossible — the drainability argument.**
   This is the core of the proof, by contrapositive:
   - `monitor_no_implies_cannotdrain_of_adequate`
     (`Nest/MonitorSoundness.lean`): no monitor fold (plus well-formedness,
     monitorability, deep adequacy) yields a drain-failure tableau
     `CannotAlwaysDrainInternalDeepRec T Q`, via the duality
     `drainrec_can_of_not_cannot` (`Nest/Drainability.lean`) and the cover
     bridge `deep_cover` + `can_enc_of_cover` (`Nest/CoverDeep.lean`).
   - `cannotdrain_implies_not_output_live` (`Nest/DrainNonLiveness.lean`):
     such a tableau refutes output liveness. A fixed-core invariant pins
     the undrainable message while the round-robin scheduler
     (`Nest/FairScheduler.lean`) is run to its dichotomy
     (`rr_run_dichotomy`): either it yields a fair infinite path that
     never fires the pinned message (`turn_run_fair`, contradicting
     liveness via `pinned_label_violates`), or it stabilises at a stuck
     state where the pinned message survives as an orphan
     (`turn_run_stuck`, contradicting liveness via
     `stuck_orphan_nonlive`).
4. **Everything persists along runs.**
   Monitorability (derived from prunability at the top, then preserved),
   deep adequacy, well-formedness, roles-present, no-self,
   half-duplex, and output liveness all transport along `net_trans`/`net_trans_star`
   (`Network.wellFormedPreserved`, `net_trans_preserves_monitorable`,
   `net_trans_preserves_deep_adequate`, `output_live_persistent`, …), so the
   bisimulation relation is closed under the steps it matches.

## 3. File map

Foundations (purely sequential):

- `Nest/SessionSyntax.lean` — `SessionType`, `substSessionType`,
  `SessionType.fv`, `IsClosed`, `NoDupl`, `Guarded`, `Contractive`,
  `WellFormed`, `NoRec`, `LeadsTo`, `ExtPath`, `Occurs`, `tRecCount`.
- `Nest/SessionLTS.lean` — `st_label`, `st_trans` and exclusion/shape lemmas
  (`sttr_out_not_inp`, `out_ne_self_of_noSelf`), `head_normal_form`, `HasEverywhere`.
- `Nest/NetworkLTS.lean` — `QueueMessage`/`Queue`/`dequeue`, `pruneAllNonP`,
  `pruneFirstInputDeepHas`, `pruneHasDeepIntAny/Ext`, `PruneAdequate`,
  `SessionTypeWithQueue`, `sq_action`, `sq_trans`, `Network`, `net_label`,
  `net_trans`, `netLTS`, `oldest_from` (oldest message from a sender +
  uniqueness and existence lemmas).
- `Nest/MonitorLTS.lean` — `mon_verdict`, `mon_tr_yes_base`, `Unfold1/UnfoldStar`,
  `IsHeadNF`, `mon_tr_yes_exist`, `mon_tr_yes_max_deriv`, `mon_tr_yes`, `mon_tr_no`,
  `monitor_fold_aux`/`monitor_fold`/`monitor_fold_val_partial`, `MonitoredSessionType`,
  `mon_trans`, `MonitoredNetwork`, `mon_net_trans`, `consistentInstrumentation`,
  `IsInternalBisimulation`, `InternallyBisimilar`.
- `Nest/NetworkLiveness.lean` — `IsHalfDuplex`, `over_trans`, `net_trans_star`,
  `InfiniteNetworkPath`, `IsFair`, `IsStuckNetwork`, `NoOrphanMessages`,
  `IsOutputLiveNetwork`, `networkBudget`, network-step preservation
  (`Network.wellFormedPreserved`, `net_trans_preserves_no_self`, …).
- `Nest/SessionUtils.lean` — substitution/no-op lemmas,
  well-formedness descent, encoder-target uniqueness
  (`mon_tr_yes_base_target_unique`, `mon_tr_yes_target_unique`),
  `monitor_fold_val_partial_eq_of_some/of_monitor_fold`, `monitor_fold_aux_append_iff`,
  `over_trans_trace`, `CanAlwaysDrainInternalDeep(Core)`.

Mid layers (scheduler → toolkit → drainability):

- `Nest/FairScheduler.lean` — round-robin drain scheduler: `round_robin_roles`,
  `rr_drain_trace`, `turnRelSeq/Lbl`, `flatSeq/Tr`, the dichotomy
  `rr_run_dichotomy` (fair infinite path via `turn_run_fair`, or
  finite-maximal stuck state via `turn_run_stuck`), `turn_reachable`;
  appendix `LabeledStar`/`Avoids`.
- `Nest/StuckWitness.lean` — `role_trace_action`, `role_trace_step`, `role_trace`,
  `aligned_exec`, `st_seq`.
- `Nest/MonitorToolkit.lean` — `max_deriv_height`,
  `mem_consistentInstrumentation`, `consistentInstrumentation_replace`,
  queue/dequeue toolkit, `comm_persists`, `dequeue_persists`,
  `output_live_persistent`.
- `Nest/Drainability.lean` (namespace `Drainability`) — the single
  `PruneStep`/`Monitorable` definitions; `Monitorable.mono/of_step`;
  failure tableaux `CannotAlwaysDrainInternalDeepSeen/Rec`;
  positive `CanAlwaysDrainInternalDeepRec`; the duality pair
  `drainrec_can_of_not_cannot` (backward: failure-free tableau builds
  drainage, needs `Monitorable`) and `drainrec_not_cannot_of_can`
  (forward, via `BroadTree` excision/transport).

Adequacy and cover:

- `Nest/SessionAdequacy.lean` — `forced_step`, `PrunableOneMsg`, `ExposedFrom`,
  `Prunable` (with `deep_has_acyclic`, bridges, lifting); `Has`
  substitution helpers; direct covers; fuel-free `go_unfold_rel` derivations with
  `go_unfold_rel.toMaximal`; `PruneAdequateU`; `monitor_fold_aux` absorption assembly.
- `Nest/CoverDeep.lean` — `has_cover`, `drainRelRec`, forced-`go_unfold_rel` existence,
  `can_enc_of_cover`, `SeenEvidence`, `deep_cover`.

Refutation and correspondence:

- `Nest/DrainNonLiveness.lean` — `FixedCoreInv`/`CoreConfig`,
  `fixedCore_*` scheduler closure, and
  `cannotdrain_implies_not_output_live`.
- `Nest/DequeueCorrespondence.lean` — `dequeue_go_split`,
  `habs_full`, `mon_dequeue_network_dequeue`,
  `network_dequeue_mon_dequeue`.
- `Nest/MonitorSoundness.lean` — `Network.Monitorable/Prunable`,
  `SessionType.DeepAdequate`, `Network.DeepAdequate` with their
  `net_trans`/`net_trans_star` preservation lemmas,
  `monitor_no_implies_cannotdrain_of_adequate`,
  `network_comm_mon_comm`, `mon_comm_network_comm`, and
  `monitor_soundness`.

Supporting material: `Nest/Examples/` (protocol examples plus the
`WallDemo` duality separating example), `Nest/Tests/` and
`Nest/NoRec/` (certified tests and the recursion-free development),
`Nest/Counterexamples/` (witnesses).

## 4. Checking the result

- Full build: `lake build Nest` (exit 0, warnings only).
- No `sorry`/`admit` in any `Nest/*.lean` file.
- `#print axioms monitor_soundness` reports only
  `[propext, Classical.choice, Quot.sound]`.

## 5. Recursion-free fragment

The recursion-free fragment of this development — the proof of
`monitor_soundness_norec`, which trades the prunability
hypothesis and the fair scheduler for the syntactic payoff of `NoRec` — is
documented separately in [OVERVIEW-NoRec.md](OVERVIEW-NoRec.md), including a
point-by-point comparison with the proof above.

# NestLean — proof overview

This file describes the mechanisation strategy for the main theorem,
`monitor_soundness_co`, and maps each proof ingredient to the `.lean`
file, definition, or lemma that provides it. Files are listed in
dependency order: each layer only builds on the layers above it.

## 1. What is proved

**Theorem** `monitor_soundness_co` (`Nest/MonitorSoundnessCo.lean`):
a network `N` that is well-formed, has no self-sends, has all roles present,
is output-live (`IsOutputLiveNetwork`), and half-duplex (`IsHalfDuplex`)
is *internally bisimilar* (coinductively, `InternallyBisimilarCo`) to its
consistent instrumentation `MN`
(`consistentInstrumentation_co N = some MN`).

The witness relation is
`R N MN := InvCo N ∧ MNhostCo MN = N ∧ AlignedCo MN`,
i.e. the network invariant, host projection (`MNhostCo` forgets monitor
states), and semantic-fold alignment (`AlignedCo`: every entry folds its
queue via `SemFoldCo`). The proof is a coinductive bisimulation argument
with four matching directions (`τ_dequeue`/`τ_comm`, each side):
`network_dequeue_mon_dequeue_co`, `network_comm_mon_comm_co`,
`mon_dequeue_network_dequeue_co`, `mon_comm_network_comm_co`.

## 2. Proof strategy

1. **Dequeue steps match via alignment.**
   `network_dequeue_mon_dequeue_co` / `mon_dequeue_network_dequeue_co`
   step `SemFoldCo` along `sq_trans.dequeue` (`SemFoldCo_dequeue`),
   preserving host projection (`MNhostCo_replace`) and alignment (case
   split on `MN_mem_replace_inv`: updated entries re-fold, the rest keep
   their folds). The monitored side uses the relational instrumentation
   bridge (`consistentInstrumentation_inv_mem_co`,
   `monitor_fold_val_partial_co_sound`).
2. **Communication steps need fresh folds for post-step configurations.**
   Forward (`network_comm_mon_comm_co`): `SemFoldCo_send` folds the
   sender's post-state, `SemFoldCo_recv_accept` folds the receiver's
   (fed by `SemFoldCo_exists_InvCo`, see 3). Backward
   (`mon_comm_network_comm_co`) mirrors this with `SemFoldCo_send_any` /
   `SemFoldCo_recv_any` replaying the observed steps.
3. **Observed co-steps are identified up to `Eqv`, never computed.**
   The observed `mon_tr_yes_co` steps furnish `Prune` derivations
   (`co_implies_Prune`), `fmon_exists` turns the induced `Ex` into finite
   `fmon` derivations, and `Prune_unique` + `SemFoldCo_eqv_tgt` identify
   them (up to `Eqv`) with the observed targets. No functionalization is
   used anywhere: targets carry their well-formedness from fold
   derivations or carried hypotheses, never from the raw relation.
4. **Folds always exist — the liveness argument.**
   `SemFoldCo_exists_InvCo` reduces every alignment obligation to
   `LiveCanDrainCo.live_can_drain`: every entry of an output-live network
   can drain its queue. This is proved by contrapositive
   (`failure_not_live`): a failing queue yields a minimal failing core
   (`CoreConfig`/`FixedCoreInv`, via `Nat.find` on the smallest failing
   queue length) whose head message can never be dequeued
   (`fixedCore_flatLbl_ne`); running the fair scheduler to its dichotomy
   either yields a fair infinite path that never fires the pinned message
   (`turn_run_fair`, contradicting liveness via `pinned_label_violates`),
   or stabilises at a stuck state where the pinned queue is a non-live
   orphan (`turn_run_stuck`, contradicting liveness via
   `stuck_orphan_nonlive`). Built on the `Drainability` predicates and the
   `FairScheduler` turn machinery.
5. **Everything persists along runs.**
   `InvCo_step` preserves the invariant along `τ` steps;
   `MNhostCo_replace` keeps host projection aligned with
   `Network.replace`; alignment is re-established per step as above. The
   initial alignment comes from consistency
   (`consistentInstrumentation_inv_mem_co`,
   `monitor_fold_val_partial_co_sound`, `fold_co_to_SemFoldCo`).
6. **Executable decision procedure.**
   `mon_tr_yes_co_fun_sound` (`Nest/MonitorCoFun.lean`: `outgoing_sound`
   + `fmon_implies_mon_tr_yes_co`) shows the finite coinductive transition
   function agrees with the relation; `mon_tr_yes_co_fun_complete` goes
   the other way (`co_implies_Prune` → `Ex_of_Prune` → alphabet/eligibility
   → `FmonCompute.residual` derivation, target unique up to
   `UnfoldEquiv` via `Prune_unique` + `eqv_implies_unfoldEquiv`).

## 3. File map

Foundations (purely sequential):

- `Nest/SessionSyntax.lean` — `SessionType`, `substSessionType`,
  `SessionType.fv`, `IsClosed`, `NoDupl`, `Guarded`, `Contractive`,
  `WellFormed`, `NoRec`, `LeadsTo`, `ExtPath`, `Occurs`, `tRecCount`.
- `Nest/SessionLTS.lean` — `st_label`, `st_trans` and exclusion/shape lemmas
  (`sttr_out_not_inp`, `out_ne_self_of_noSelf`), `IsHeadNF`,
  `Unfold1`/`UnfoldStar`.
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
  `over_trans_trace`, `CanAlwaysDrainInternalDeep(Core)`. (`LeadsTo`
  paths and `graftFold` live in `Nest/NoRec/NoRecUtils.lean`.)
- `Nest/MonitorCo.lean` — the coinductive maximal relation
  `mon_tr_yes_max_deriv_co` (coverage/order per branch pair plus one
  corecursive call, with target folding) and the `mon_tr_yes_co`
  abbreviation.
- `Nest/MonitorCoBase.lean` — shared session-type infrastructure:
  acceptability (`Ex`), `session_induction`, `PruneStep`,
  environments/substitution, `traversalNodes` closure, and
  branch filtering (`KRint`/`KRext`).

Mid layers (scheduler → executable relation → toolkit):

- `Nest/FairScheduler.lean` — round-robin drain scheduler: `round_robin_roles`,
  `rr_drain_trace`, `turnRelSeq/Lbl`, `flatSeq/Tr`, the dichotomy
  `rr_run_dichotomy` (fair infinite path via `turn_run_fair`, or
  finite-maximal stuck state via `turn_run_stuck`), `turn_reachable`;
  appendix `LabeledStar`/`Avoids`.
- `Nest/MonitorCoFun.lean` — the executable coinductive transition
  function `mon_tr_yes_co_fun` (`FmonCompute.outgoing`/`residual`/`observe`)
  with soundness (`mon_tr_yes_co_fun_sound`) and completeness
  (`mon_tr_yes_co_fun_complete`, target unique up to `UnfoldEquiv`),
  executable well-formedness (`wfCheck` + soundness, `guardedCheck`),
  and the eligibility decision procedure.
- `Nest/MonitorCoRel.lean` — the relational base: fold relation (`fmon`),
  pruning (`Prune`), and type equivalence (`Eqv`), with head
  normalisation, base-case transfer, and well-formedness infrastructure;
  shared by the executable development and the coinductive soundness chain.
- `Nest/MonitorToolkit.lean` — `max_deriv_height`,
  `mem_consistentInstrumentation`, `consistentInstrumentation_replace`,
  queue/dequeue toolkit, `comm_persists`, `dequeue_persists`,
  `output_live_persistent`.
- `Nest/MonitorToolkitCo.lean` — coinductive twins of the
  consistent-instrumentation bridge lemmas
  (`mem_consistentInstrumentation_co`,
  `consistentInstrumentation_inv_mem_co`,
  `consistentInstrumentation_filter/replace_co`), with the relational
  `monitor_fold_val_partial_co` and `consistentInstrumentation_co` in
  place of the finite versions. No functionalization is used.

The `Co` chain (relational soundness):

- `Nest/MonitorLTSCo.lean` — the relational coinductive LTS: `mon_tr_co`
  uses `mon_tr_yes_co` on the yes-branch (`good_send`/`good_recv`) and
  finite `mon_tr_no` on the no-branch; `mon_trans_co`,
  `mon_net_trans_co`, `mnetLTS_co`; relational queue fold
  `monitor_fold_aux_co`/`monitor_fold_co`,
  `monitor_fold_val_partial_co` (+ soundness).
- `Nest/SemFoldCo.lean` — the `SemFoldCo` alignment invariant plus
  coinductive twins of the head-normalisation, base, alignment, and
  pruning-congruence helpers (`hnf_wf_co`, `hnf_exists_co`,
  `base_eqv_co`, `alignInt_mem_r_co`, `alignInt_wf_co`,
  `alignExt_wf_co`, `Ex_eqv_co`, `KRint_left_co`, `KRext_left_co`,
  `PruneN_eqv_l_co`, `Prune_eqv_l_co`, `Prune_base_co`), send/recv/dequeue
  stepping (`SemFoldCo_send`, `SemFoldCo_recv_accept`,
  `SemFoldCo_send_any`, `SemFoldCo_recv_any`, `SemFoldCo_dequeue`),
  uniqueness up to `Eqv` (`SemFoldCo_unique`, `SemFoldCo_eqv_tgt`),
  `SemFoldCo_exists_of_Can`, `QueueRunCo`, and
  `fold_co_to_SemFoldCo`.
- `Nest/FoldExistsCo.lean` — finite traversal closure
  (`finite_traversal` over `traversalNodes`), `pfx_build`, and Fold
  existence (`fmon_exists_of_finite`, `fmon_exists`).
- `Nest/LiveCanDrainCo.lean` — liveness implies drainability: `Fails`,
  the minimal-core invariant (`FixedCoreInv`/`CoreConfig`), scheduler
  non-firing lemmas (`fixedCore_flatLbl_ne`), the refutation
  (`pinned_label_violates`, `stuck_orphan_nonlive`), and the two main
  results `failure_not_live` (by contrapositive) and `live_can_drain`.
- `Nest/MonitorSoundnessCo.lean` — the invariant `InvCo` (with
  `InvCo_step`), host projection (`MNhostCo` + commutation/membership
  lemmas), alignment (`AlignedCo`), the witness relation `R`, the
  four correspondence lemmas, and `monitor_soundness_co`.

Ports in `SemFoldCo`, `FoldExistsCo`, `LiveCanDrainCo`, and
`MonitorCoFun(Aux)` build on work credited to Jules Jacobs
<jules.jacobs@inf.ethz.ch>, Nate Foster <nate.foster@epfl.ch>,
and Kristýna Petrlíková <auburn@kam.mff.cuni.cz>;
see per-file headers for details.

Supporting material: `Nest/Examples/` (protocol examples plus the
`WallDemo` duality separating example), `Nest/Tests/` (including the
script-generated `MonitorCo` corpus tests `tNN_sound_*`), `Nest/NoRec/`
(certified tests, the recursion-free development, and `NoRecUtils` with
the relocated `LeadsTo`/graft utilities), `Nest/Counterexamples/`
(witnesses).

### Example networks

Every protocol example from the Nest tool implementation has a Lean
counterpart in `Nest/Examples/` with an empty-queue `Net`, proven
well-formed (`Net_wellFormed`), with no self-sends (`Net_noSelf`), all
roles present (`Net_rolesPresent`), consistently instrumentable
(`Net_consistent`), half-duplex (`Net_halfDuplex`), and output-live
(`Net_outputLive`). All ten networks are co-monitorable via finite-state
monitors (`Network.MonitorableCo`, `Net_monitorable_co` in
`Nest/Examples/MonitorableCoExamples.lean` through
`MonitorableCo.of_check`).

| Nest tool example | Lean module | Half-duplex / output-live |
|---|---|---|
| [01_bookreview.scala](NEST/nest/nest_scala/src/main/scala/examples/01_bookreview.scala) | `Nest/Examples/Bookreview.lean` | same file |
| [02_store.scala](NEST/nest/nest_scala/src/main/scala/examples/02_store.scala) | `Nest/Examples/Store.lean` | `StoreHD` / `StoreOL` |
| [03_vpn.scala](NEST/nest/nest_scala/src/main/scala/examples/03_vpn.scala) | `Nest/Examples/Vpn.lean` | `VpnHD` / `VpnOL` |
| [04_firewall.scala](NEST/nest/nest_scala/src/main/scala/examples/04_firewall.scala) | `Nest/Examples/Firewall.lean` | same file |
| [05_dns.scala](NEST/nest/nest_scala/src/main/scala/examples/05_dns.scala) | `Nest/Examples/Dns.lean` | same file |
| [06_auction.scala](NEST/nest/nest_scala/src/main/scala/examples/06_auction.scala) | `Nest/Examples/Auction.lean` | same file |
| [07_cdn.scala](NEST/nest/nest_scala/src/main/scala/examples/07_cdn.scala) | `Nest/Examples/Cdn.lean` | same file |
| [08_sip.scala](NEST/nest/nest_scala/src/main/scala/examples/08_sip.scala) | `Nest/Examples/Sip.lean` | same file |
| [09_pop3.scala](NEST/nest/nest_scala/src/main/scala/examples/09_pop3.scala) | `Nest/Examples/Pop3.lean` | same file |
| [10_game.scala](NEST/nest/nest_scala/src/main/scala/examples/10_game.scala) | `Nest/Examples/Game.lean` | `GameHD` / `GameOL` |

## 4. Checking the result

- Full build: `lake build Nest` (exit 0, warnings only).
- No `sorry`/`admit` in any `Nest/*.lean` file.
- `#print axioms monitor_soundness_co` reports only
  `[propext, Classical.choice, Quot.sound]`.

## 5. Recursion-free fragment

The recursion-free fragment of this development — the proof of
`monitor_soundness_norec`, which trades output-liveness hypotheses and
the fair scheduler for the syntactic payoff of `NoRec` — is documented
separately in [OVERVIEW-NoRec.md](OVERVIEW-NoRec.md), including a
point-by-point comparison with the proof above. The finite maximal-derivation
proof `monitor_soundness` (which additionally assumes prunability) is
superseded by the coinductive monitor soundness result above; see
[OVERVIEW-ecoop26.md](OVERVIEW-ecoop26.md) for its overview.

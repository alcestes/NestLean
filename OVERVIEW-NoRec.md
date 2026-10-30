# NoRec soundness — proof overview

This file describes the mechanisation strategy for the recursion-free
fragment theorem, `monitor_soundness_norec`, and maps each proof ingredient
to the `.lean` file, definition, or lemma that provides it. Files are listed
in dependency order. For the general (possibly recursive) soundness theorem,
see [OVERVIEW.md](OVERVIEW.md); the differences between the two proofs are
highlighted in §4 below.

## 1. What is proved

**Theorem** `monitor_soundness_norec`
(`Nest/NoRec/MonitorSoundnessNoRec.lean`):
a network `N` that is recursion-free (`Network.NoRec`), well-formed, has all
roles present, has no self-sends, is output-live (`IsOutputLiveNetwork`),
and half-duplex (`IsHalfDuplex`) is internally bisimilar
(`InternallyBisimilar`) to its consistent instrumentation `MN`
(`consistentInstrumentation N = some MN`).

The witness relation is the same as in the general proof:
`R N' MN' := consistentInstrumentation N' = some MN' ∧ net_trans_star N N'`
(consistency plus `τ*`-reachability), and each internal step is matched by
one of four correspondence lemmas.

## 2. Proof strategy

1. **Dequeue steps match via absorption transfer.**
   `type_mon_dequeuing_norec` and `mon_type_dequeuing_norec`
   (`Nest/NoRec/CommCorrespondence.lean`, section `DequeueCorrespondence`)
   move a `τ_dequeue` across the instrumentation in both directions.
   The consistency of the target is the general transfer
   `monitor_fold_absorb_dequeue_transfer_norec` (`Nest/NoRec/DeepComplement.lean`),
   fed by the scan shape (`queue_dequeue_some_iff`, which supplies freshness).
2. **Communication steps match unless the monitor rejects.**
   `network_comm_mon_comm_norec` / `mon_comm_network_comm_norec`
   (`Nest/NoRec/CommCorrespondence.lean`) move a `τ_comm` across, but each
   side needs two folds to exist: sender absorption
   (`monitor_fold_aux_out_aux_norec`, from `Nest/NoRec/NoRecEncoder.lean`) and
   receiver acceptance (an `mon_tr_yes` step, pinned by
   `mon_tr_yes_target_unique`).
3. **Missing folds are impossible — the drain-failure argument.**
   If no monitor fold exists for a post-state queue,
   `mon_reject_implies_nodrain_norec` (`Nest/NoRec/DeepComplement.lean`)
   builds a `CannotAlwaysDrainInternalDeep` witness — via
   `drain_implies_mon_exists_accepts_norec` (`Nest/NoRec/DrainAccept.lean`):
   draining implies monitor acceptance, so rejection implies no drain.
   The duality `deep_iff_not_cannot_norec` (`Nest/NoRec/DeepComplement.lean`,
   from the decision procedure `deep_or_cannot_norec`) turns this into
   `¬ CanAlwaysDrainInternalDeep`, and `no_deep_drain_no_output_liveness_hd_norec`
   (`Nest/NoRec/SteerLoop.lean`) refutes output-liveness (or half-duplex),
   contradicting the hypotheses.
4. **Everything persists along runs.**
   `NoRec`, well-formedness, roles-present, no-self, half-duplex, and output
   liveness all transport along `net_trans`/`net_trans_star`
   (`net_trans_preserves_norec`, `net_trans_preserves_norec`,
   `Network.wellFormedPreserved`, `output_live_persistent`, …), so the
   bisimulation relation is closed under the steps it matches.

## 3. File map

Foundations (recursion-free toolkit):

- `Nest/NoRec/NoRecToolkit.lean` — `Network.NoRec`, step/network
  preservation (`net_trans_preserves_norec`, `net_trans_preserves_norec`),
  size-shrink (`st_trans_size_lt_of_norec`), budgets (`budget_step_norec`),
  stuck-reachability (`exists_stuck_reachable_of_NoRec`), liveness stability
  (`IsOutputLiveNetwork_stable_of_NoRec`, `norec_live_infinite_vacuous`).
- `Nest/NoRec/VacuousRec.lean` — `SessionType.VacuousRec` /
  `Network.VacuousRec` (every `tRec` binds an unused variable) with its
  preservation/termination mirrors and the `VacuousRec.of_NoRec` bridge.
- `Nest/NoRec/NoRecEncoder.lean` — `IsBalancedW`,
  `pruneFirstInputDeep`, `PruneAdequate.of_vacuous_everywhere`,
  `monitor_fold_aux_out_aux_norec` (send absorption under `NoRec`+`NoDupl`).
- `Nest/NoRec/PruneFunctions.lean` — fuel-free prune functions
  (`pruneFirstInputHas/Go`, `pruneGoInt/Ext`, …), the single home for these
  definitions.

Drainability core:

- `Nest/NoRec/DrainCore.lean` — over_trans preservation under `NoRec`,
  choice-function core bridges (`CanAlwaysDrainInternalDeepCore.toDeep`,
  `.toCore`, `.suffix`), `oldest_from`/queue order, branch-target uniqueness
  (`ext_target_unique_norec`, `int_target_unique_norec`), the `Cannot` core
  and absence-implies-no-dequeue.
- `Nest/NoRec/PrunePreservation.lean` — dequeue-scan skipping, over_trans vs
  `st_trans` step classification (`deep_prepend_*`), prune-function key/map
  lemmas, `pruneGo` NoDupl/`NoRec` preservation.
- `Nest/NoRec/DrainSurvival.lean` — `drain_survives_*` (pruning preserves
  drainability, NoRec and vacuous versions), `mon_yes_prune_deep_mp`
  (adequacy computes a monitor-yes step),
  `prune_first_input_deep_go_preserves_vacuous_rec`, `cannot_prepend_*`.

Acceptance, duality, steering:

- `Nest/NoRec/DrainAccept.lean` — `drain_implies_mon_exists_accepts_vacuous`
  (queue induction with `tRecCount` fuel) and the `NoRec` bridge
  `drain_implies_mon_exists_accepts_norec`.
- `Nest/NoRec/DeepComplement.lean` — `dequeue_scan_key_backprop_norec`,
  drains/suffix bridges, `deep_or_cannot_norec` (decision procedure),
  `deep_iff_not_cannot_norec`, `monitor_fold_absorb_dequeue_transfer_norec`,
  `mon_reject_implies_nodrain_norec`.
- `Nest/NoRec/SteerLoop.lean` — tEnd starters, queue persistence,
  dequeue blocking, `over_trans_traces` surgery lemmas, append persistence,
  spec-only transport, steering, loop liveness; funnels to
  `no_deep_drain_no_output_liveness_hd_norec`.

Assembly:

- `Nest/NoRec/CommCorrespondence.lean` — all four correspondence directions
  (dequeue pair + `network_comm_mon_comm_norec` +
  `mon_comm_network_comm_norec`).
- `Nest/NoRec/MonitorSoundnessNoRec.lean` — `monitor_soundness_norec`.

Supporting material: `Nest/NoRec/Tests/` (e.g. `OverapproxTest`),
`Nest/NoRec/Counterexamples/` (separation witnesses such as
`CounterexampleMonitorDiamond`, `CounterexampleDrainReorder`).

## 4. Differences with the proof of `monitor_soundness`

| Aspect | `monitor_soundness` ([OVERVIEW.md](OVERVIEW.md)) | `monitor_soundness_norec` (here) |
|---|---|---|
| Hypotheses | `N.Prunable` (deep prunability, which also yields `N.Monitorable` via `prunable_implies_monitorable`) + liveness + half-duplex | `N.NoRec` (syntactic, decidable) + liveness + half-duplex; **no** monitorability/adequacy hypotheses |
| Termination argument | Round-robin scheduler (`FairScheduler`): `rr_run_dichotomy` yields a fair infinite path (`turn_run_fair`) or a stuck state (`turn_run_stuck`) | Free from `NoRec`: steps go to strict subterms (`st_trans_size_lt_of_norec`, budgets), infinite internal paths don't exist (`noInfiniteInternalPath_of_NoRec`), stuck states are reachable (`exists_stuck_reachable_of_NoRec`) — **no scheduler, no fairness machinery** |
| Drain-failure ⇒ non-live | Fixed-core invariant + scheduler closure (`DrainNonLiveness`: `FixedCoreInv`, `fixedCore_*`, `cannotdrain_implies_not_output_live`) | Steering tableau (`SteerLoop`) funnelling to `no_deep_drain_no_output_liveness_hd_norec` |
| Drainability duality | `Can ⇔ ¬Cannot` via failure tableaux with visited sets + `BroadTree` excision/transport, measured by the `Monitorable` closure (`Drainability`) | `deep_iff_not_cannot_norec` via the decision procedure `deep_or_cannot_norec` + drains/suffix bridges (`DeepComplement`) |
| Adequacy / cover layer | Whole `SessionAdequacy` + `CoverDeep` apparatus: `Prunable`, `forced_step`, `go_unfold_rel`, maximal derivations, `SeenEvidence`, `has_cover`, `deep_cover`, `can_enc_of_cover` | None of it: `drain_implies_mon_exists_accepts_norec` (`DrainAccept`, via the vacuous assembly) suffices |
| Dequeue absorption | `habs_full` along `UnfoldStar` chains (`DequeueCorrespondence`) | `monitor_fold_absorb_dequeue_transfer_norec` (`DeepComplement`) |
| Comm absorption | `monitor_fold_aux_out_aux_general` (needs adequacy hypotheses) | `monitor_fold_aux_out_aux_norec` (needs only `NoRec`+`NoDupl`) |
| Vacuous recursion | Not present (general proof handles `tRec` via adequacy) | Parallel `VacuousRec` toolkit bridging `NoRec` types into the vacuous drain assembly |

In short: the general proof pays for arbitrary recursion with a semantic
finiteness hypothesis (`Prunable`/`DeepAdequate`, with `Monitorable` derived
rather than assumed), a cover
derivation layer, and a fair scheduler; the NoRec proof replaces all three
with the syntactic payoff of recursion-freedom — every step shrinks the
session type, so drainage, termination, and stuck-reachability hold by
plain induction.

## 5. Checking the result

- Full build: `lake build Nest` (exit 0, warnings only) covers the whole
  `Nest/NoRec/` tree.
- No `sorry`/`admit` in any `Nest/NoRec/*.lean` file.
- `#print axioms monitor_soundness_norec` reports only
  `[propext, Classical.choice, Quot.sound]`.

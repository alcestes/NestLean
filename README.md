# Nest — Network-Enforced Session Types, Mechanised

This is the Lean 4 mechanisation of the coinductive monitor theory of NEST:
an output-live, half-duplex network is internally bisimilar (coinductively)
to its consistent instrumentation. The main theorem is `monitor_soundness_co`
(`Nest/MonitorSoundnessCo.lean`): well-formed, no-self-send, roles-present,
output-live, half-duplex networks are internally bisimilar
(`InternallyBisimilarCo`) to their consistent instrumentation
(`consistentInstrumentation_co N = some MN`). The full proof scripts, with all
auxiliary lemmas proved and no `sorry`/`admit`/`axiom` anywhere, are in `Nest/`.

Build instructions:

- `lake exe cache get`
- `lake build Nest`

**Note:** a full build takes around 26 minutes on an AMD Ryzen 7 PRO 4750U with
32 GB of RAM. Most of the time is spent on the larger examples under
`Nest/Examples/`, which can be commented out from `Nest.lean` for a faster
build.

Three network-level soundness theorems are proved, with standard axioms only
(`[propext, Classical.choice, Quot.sound]`):
- `monitor_soundness_co` (`Nest/MonitorSoundnessCo.lean`): the general,
  coinductive case — as stated above.
- `monitor_soundness` (`Nest/MonitorSoundness.lean`): the finite,
  maximal-derivation variant — the same statement with an additional
  deep-prunability hypothesis (`Network.Prunable`); monitorability follows
  from prunability via `prunable_implies_monitorable`. It was the main
   result of the ECOOP 2026 paper, where no prunability hypothesis was
   stated. It is superseded by the coinductive monitor soundness result
   (`monitor_soundness_co` above); see [OVERVIEW-ecoop26.md](OVERVIEW-ecoop26.md).
- `monitor_soundness_norec` (`Nest/NoRec/MonitorSoundnessNoRec.lean`): the
  recursion-free case — same statement with the semantic `Prunable`
  hypothesis traded for syntactic `Network.NoRec` (every step shrinks the
  session type, so drainage, termination, and stuck-reachability hold by
  plain induction, with no scheduler or fairness machinery).

For the structure of the mechanised proofs — dependency order, file maps,
and where each paper step lands in Lean — see
[OVERVIEW.md](OVERVIEW.md) for the coinductive proof (the main result),
[OVERVIEW-ecoop26.md](OVERVIEW-ecoop26.md) for the superseded finite proof, and
[OVERVIEW-NoRec.md](OVERVIEW-NoRec.md) for the recursion-free fragment.

## Key decisions in the Lean formalisation

- **Session types as lists of branches.** The paper uses indexed sums with
  non-empty index sets and pairwise distinct labels (`⊕_{i∈I}` / `&_{i∈I}`,
  the ECOOP 2026 paper, Def. local-types). Lean (`Nest/SessionSyntax.lean`) uses
  `internalChoice : List (Role × Lab × DataSort × SessionType)` /
  `externalChoice : Role → List (Lab × DataSort × SessionType)`.
  Non-emptiness + no-duplicates are enforced by `SessionType.NoDupl`
  (hence `SessionType.WellFormed = NoDupl ∧ IsClosed ∧ Contractive`).

- **Substitution for recursion variables.** `substSessionType` is structural
  recursion with `String` equality (shadowing guard `if X = Y` in `tRec`).
  The paper uses `subst{T}{X}{μX.T}` in `S-Rec`/`STMon-Rec` under global
  closed + guarded assumptions. Lean makes `fv` / `Guarded` / `Contractive`
  explicit, with banked preservation lemmas (`fv_subst_aux`,
  `NoDupl_subst`, `IsClosed_subst`, `IsContractive_subst`).

- **`MonitoredSessionType` as a product.** `Nest/MonitorLTS.lean`:
  `abbrev MonitoredSessionType := SessionTypeWithQueue × SessionType`,
  i.e. `((T, Q), M)`. This matches the paper's pairing `⟨T̈ | M⟩`
  (the ECOOP 2026 paper, Def. st-monitor) directly.

- **Queue congruence as selective dequeue.** The paper has `SQ-Deq` with an
  explicit congruence `≡` swapping messages of different senders
  (the ECOOP 2026 paper, Def. local-semantics). Lean has no `≡`; instead
  `Queue.dequeue.go` scans past other-sender messages and blocks on a
  same-sender mismatch, with `queue_dequeue_some_iff` giving the
  `seen ++ [msg] ++ left` shape used by the dequeue-transfer lemmas.

- **`consistentInstrumentation` as a partial `def`.** Paper `mon(N)`
  (the ECOOP 2026 paper, Def. consistent-mon-instr):
  `{ pᵢ ↦ ⟨T̈ᵢ | ⟦T̈ᵢ⟧⟩ }`, where `⟦(T, Q)⟧` is the queue fold
  (`Def. monitor-state-st-queue`), undefined if `⟦T⟧` rejects some message
  in `Q`. Lean (`Nest/MonitorLTS.lean`): `consistentInstrumentation :
  Network → Option MonitoredNetwork` by recursion on the role list, using
  `monitor_fold_val_partial stq : Option SessionType` (choice over the
  relational `monitor_fold`/`monitor_fold_aux`). `consistentInstrumentation N =
  some MN` iff every entry folds. Step targets carry the *new* fold value
  `Mp'`/`Mq'` (via `mon_tr_yes` +
  `monitor_fold_val_partial_eq_of_monitor_fold`), not `stq'.1`.

- **Encoder with explicit maximality.** Paper `STMon-IntPfx`/`STMon-ExtPfx`
  have a "maximal `∅ ≠ K ⊆ I`" side condition and `STMon-Bad` as rejection.
  Lean splits this into `mon_tr_yes_base` (rigid `intC`/`extC`/`tRec`),
  `mon_tr_yes_exist` (existential kept-lists), `mon_tr_yes_max_deriv`
  (hereditary maximality + coverage + source-order `Sublist`), `mon_tr_yes :=
  ∃ derivation, Maximal`, and `mon_tr_no` (`∀ V, ¬ mon_tr_yes T γ V`) for
  `STMon-Bad`. Determinism is `mon_tr_yes_target_unique` (needs only `NoDupl`).

- **`Prunable`, the one hypothesis with no paper counterpart.** The paper
  states maximality as a side condition and never asks whether the
  monitor's verdict can actually be computed. The mechanisation must
  compute it: `monitor_fold` works by pruning the session type, and on
  recursive types naive pruning can unfold `tRec` forever. `Prunable`
  (`Nest/SessionAdequacy.lean`, lifted to networks as `Network.Prunable`)
  is the certificate saying "this type can be pruned": every branch target
  and every unfolded `tRec` body is prunable (a `seen` list bounds
  recursion — fresh binders unfold once, revisits cut), and every message
  the type can expose (`ExposedFrom`) is one-message prunable
  (`PrunableOneMsg` — no reachable cycle in the `Has`-filtered
  `forced_step` relation). It is used exactly where the general proof
  needs a verdict to exist: `Network.DeepAdequate.of_Prunable` turns it
  into adequate fuel, after which `deep_cover` + `can_enc_of_cover`
  build the monitor fold that keeps `comm` steps matchable. In other
  words, it rules out "the monitor has no verdict" for recursive types —
  the case the paper's side condition assumes away — while the `NoRec`
  proof needs none of it (recursion-freedom gives termination for free).

- **Recursion unfolding machinery.** Paper has `unfold(T)` (the ECOOP 2026
  paper, Def. st-unfolding) plus `S-Rec`/`STMon-Rec`. Lean has `st_trans.tRec`,
  `mon_tr_yes_base.tRec` / `mon_tr_yes_exist.unfold` / `mon_tr_yes_max_deriv.unfold`,
  plus `Unfold1`/`UnfoldStar`, `HNF`, `spine`, `unfoldStar_normal_exists`
  (closed contractive types reach head-normal form). The `NoRec` fragment
  prunes all `tRec` arms by `cases hNR` and uses size induction instead.

- **Networks as flat role lists.** Paper networks are `N ⏐ N'` / `⟨p | T̈⟩`
  with `Net-Par`/`Net-Comm` (the ECOOP 2026 paper, Def. network). Lean
  (`Nest/NetworkLTS.lean`): `abbrev Network := List (Role × SessionTypeWithQueue)`,
  `MonitoredNetwork := List (Role × MonitoredSessionType)`, updates by
  `Network.replace` / `MonitoredNetwork.replace` (cons + filter). There is no
  `pair`/`par` structural induction; bridge lemmas
  (`mem_consistentInstrumentation`, `consistentInstrumentation_inv_mem`,
  `consistentInstrumentation_replace/filter`) do list induction, and
  `net_trans`/`mon_net_trans` cases replace `Net-Par`/`MNet-Par` inversion.

- **Output-liveness / half-duplex are real definitions.** Paper:
  `Def. live-net` (network paths, fair paths items `fair:send`/`fair:recv`,
  output-live paths, `N` output-live iff every fair path is output-live) and
  `Def. half-duplex-net` (the ECOOP 2026 paper: `τ*`-reachable `Qᵢ ∋ pⱼ ⇒ Qⱼ ∌ pᵢ`).
  Lean (`Nest/NetworkLiveness.lean`): `IsFair`, `IsOutputLiveInfinitePath`,
  `IsOutputLiveNetwork := infinite-path liveness ∧ (τ*-reachable stuck ⇒
  NoOrphanMessages)`. The stuck conjunct is load-bearing because
  `InfiniteNetworkPath` is `ℕ`-indexed (no finite maximal paths); without it
  stuck-with-orphan networks are vacuously live. `IsHalfDuplex` is the
  `τ*` + `QueueContainsFrom` formulation. `output_live_persistent`
  (`Nest/MonitorToolkit.lean`), `IsHalfDuplex.star`, and
  `net_trans_star_preserves_{well_formed,norec,no_self,roles_present}` transfer
  invariants along the witness star. Nothing is `True`; no `trivial`
  subnet calls.

- **Well-formedness side conditions.** `Network.WellFormed = Nodup ∧
  (∀ entries, SessionType.WellFormed) ∧ SenderClosed`. The `NoRec`
  soundness additionally requires `N.NoRec`, `N.RolesPresent` (send targets
  present, so sends replay as `τ_comm`), and `N.NoSelf` (`¬ T.Occurs q`,
  the paper's "roleP does not occur in T̈" side condition, used via
  `out_ne_self_of_noSelf` for `p ≠ q`).

- **Internal bisimulation, generalised.** Paper `Def. internal-bisim` is
  already formal (annotation `φ` distinguishing `τ`-labels, LR/RL clauses;
  relation `R = {(Nᵢ, mon(Nᵢ)) | N ─τ*→ Nᵢ}`, the ECOOP 2026 paper's
  proof-net-mon-bisim relation). Lean (`Nest/MonitorLTS.lean`): heterogeneous
  `IsInternalBisimulation isLbl₁ isLbl₂ lblMap lts₁ lts₂ r` +
  `InternallyBisimilar N MN` instantiating `is_internal_net_label` /
  `is_internal_mon_net_label` / `netLabelToMonNetLabel` / `netLTS` / `mnetLTS`.
  `is_internal_*` are `match … with τ_dequeue/τ_comm => True | _ => False`.

- **`cases` on the label in `monitor_soundness_norec`.** As in the paper's
  dequeue/comm × LR/RL case split (the ECOOP 2026 paper's soundness proof),
  the Lean proof
  (`Nest/NoRec/MonitorSoundnessNoRec.lean`) does `cases μ₁`/`cases μ₂`:
  `io_send`/`io_recv` (resp. `io_yes_send`,
  `io_yes_recv`, `io_no_out`, `io_no_inp`) are discharged by `exfalso`
  with `hIntLbl₁`/`hIntLbl₂`; `τ_dequeue`/`τ_comm` go through the four
  correspondence lemmas below, extending the `net_trans_star N N'` witness.

## Key differences between the Lean formalisation and the paper

### Definitions

| Aspect | ECOOP 2026 paper | Lean (see [OVERVIEW.md](OVERVIEW.md) for the file map) |
|--------|---------------------------|---------------------------------------|
| Session type branches | Indexed sets `⊕_{i∈I}` / `&_{i∈I}`, `I ≠ ∅`, distinct labels | `List (Role × Lab × DataSort × SessionType)` / `List (Lab × DataSort × SessionType)`; non-empty + nodup via `NoDupl`/`WellFormed` |
| Recursion substitution | `subst{T}{X}{μX.T}` under closed/guarded | Concrete `substSessionType : SessionType → String → SessionType → SessionType` + `fv`/`Guarded`/`Contractive` + preservation lemmas |
| Queue consumption | `SQ-Deq` + congruence `≡` (swap different senders) | `Queue.dequeue.go` selective dequeue; `queue_dequeue_some_iff` shape lemma; no `≡` |
| Network labels | `netIOLab(p,γ)` unified send/recv, `netDequeueLab(p,q,l,S)`, `netCommLab(p,q,l,S)` | Split `net_label`: `io_send`, `io_recv`, `τ_dequeue`, `τ_comm`; `ext_tag = send \| recv` underlies both; internal = `τ_*` by `match` |
| Monitored network labels | `mnetIOLabYes/No(p,γ)`, `mnetDequeueLab`, `mnetCommLab` | Split `mon_label` (`yes_send`, `yes_recv`, `no_out`, `no_inp`, `silent`) and `mon_net_label` (`io_yes_send`, `io_yes_recv`, `io_no_out`, `io_no_inp`, `τ_dequeue`, `τ_comm`) via `mon_net_label.ofmon_label` |
| Monitor fold | Partial map `⟦(T,Q)⟧`: fold `⟦T⟧ ─yes(Q)→ ⟦T'⟧`, undefined on rejection | Both: relational `monitor_fold_aux : Queue → SessionType → SessionType → Prop` / `monitor_fold`, and `noncomputable monitor_fold_val_partial : _ → Option SessionType` with `monitor_fold_val_partial_eq_of_some/of_monitor_fold` |
| `consistentInstrumentation` target | `⟦T'⟧` from new `(T',Q')` | `monitor_fold_val_partial (T',Q') = some M'` (new fold value); never `stq'.1` alone |
| Output-liveness / half-duplex | Paths + fairness + queue conditions; half-duplex in appendix | `IsOutputLiveNetwork` (infinite-fair + stuck-no-orphans), `IsHalfDuplex` (`τ*` + `QueueContainsFrom`); plus `WellFormed`/`NoRec`/`NoSelf`/`RolesPresent` for the `NoRec` theorem |
| `IsInternalBisimulation` | Formal def with `φ` annotation, LR/RL clauses | Heterogeneous 6-explicit-argument predicate + `InternallyBisimilar` + `netLabelToMonNetLabel` |

### Proof structure (superseded finite proof)

| Aspect | ECOOP 2026 paper | Lean (general proof — superseded by the coinductive result, [OVERVIEW-ecoop26.md](OVERVIEW-ecoop26.md)) |
|--------|----------------------|----------------------------------------------------------|
| Witness relation | `R = {(Nᵢ, mon(Nᵢ)) \| N ─τ*→ Nᵢ}` | Same shape in `MonitorSoundness.monitor_soundness`: `R N' MN' := consistentInstrumentation N' = some MN' ∧ net_trans_star N N'` |
| `type_mon_dequeuing` | Inversion of `Net-Dequeue`/`SQ-Dequeue`, `unfold(T)` + `STMon-Rec`/`STMon-ExtC`, `mon-trans-congruent` giving `⟦T̈⟧ = ⟦T̈'⟧` | `DequeueCorrespondence.network_dequeue_mon_dequeue`: `queue_dequeue_some_iff` shape + `habs_full` absorption along `UnfoldStar` chains (`absorb_transfer_headnormal`, `maxRecover_unfold`), step is `mon_net_trans.dequeue` (monitor unchanged), consistency via `consistentInstrumentation_replace` |
| `mon_type_dequeuing` | "By inversion, we infer the same shape…" | `DequeueCorrespondence.mon_dequeue_network_dequeue`: generalise-then-`cases` on `mon_net_trans`, same transfer as forward |
| Forward/backward `comm` | Dequeue case + comm case using `type-send-mon-send` (`STMon-IntC`) and `live-hd-net-enqueue-mon-enqueue` (liveness + half-duplex by contradiction) | `MonitorSoundness.network_comm_mon_comm` / `mon_comm_network_comm`: send side via `monitor_fold_aux_out_aux_general` (needs adequacy hypotheses) once sender absorption is known; receive side (and sender absorption) via `monitor_no_implies_cannotdrain_of_adequate` (`Prunable` → `DeepAdequate` → `deep_cover` + `can_enc_of_cover`) + `cannotdrain_implies_not_output_live` (fixed core + fair scheduler to `turn_run_fair`/`turn_run_stuck`) contradicting `output_live_persistent` / `IsHalfDuplex.star`; backward pins the monitor target with `mon_tr_yes_target_unique` |
| Recursion unfolding | `unfold(T)` lemma + `STMon-Rec` | `st_trans.tRec` / `mon_tr_yes_*` unfold arms + `UnfoldStar`/`HNF`/`spine` theory; recursive types handled via adequacy (`Prunable`), never pruned |
| Main theorem case analysis | `dequeue` LR, `dequeue` RL, `comm` LR, `comm` RL | `monitor_soundness`: `cases μ₁`/`cases μ₂`; non-`τ` labels `exfalso` via `is_internal_*`; `τ_dequeue`/`τ_comm` via the four lemmas above (`network_dequeue_mon_dequeue`, `network_comm_mon_comm`, `mon_dequeue_network_dequeue`, `mon_comm_network_comm`) |
| Scope | All closed guarded types | `Prunable` (→ `DeepAdequate`, and → `Monitorable` via `prunable_implies_monitorable`) + `WellFormed` + `RolesPresent` + `NoSelf` + output-live + half-duplex + `consistentInstrumentation N = some MN`; drain-failure argument via failure tableaux + cover (`Drainability`, `CoverDeep`) and fair scheduler (`FairScheduler.rr_run_dichotomy`) |

### Proof structure (recursion-free `NoRec` chain)

| Aspect | ECOOP 2026 paper | Lean (`NoRec` chain, [OVERVIEW-NoRec.md](OVERVIEW-NoRec.md)) |
|--------|----------------------|----------------------------------------------------------|
| Witness relation | `R = {(Nᵢ, mon(Nᵢ)) \| N ─τ*→ Nᵢ}` | Same shape in `MonitorSoundnessNoRec.monitor_soundness_norec`: `R N' MN' := consistentInstrumentation N' = some MN' ∧ net_trans_star N N'` |
| `type_mon_dequeuing` | Inversion of `Net-Dequeue`/`SQ-Dequeue`, `unfold(T)` + `STMon-Rec`/`STMon-ExtC`, `mon-trans-congruent` giving `⟦T̈⟧ = ⟦T̈'⟧` | `CommCorrespondence.network_dequeue_mon_dequeue_norec`: `queue_dequeue_some_iff` shape + `monitor_fold_absorb_dequeue_transfer_norec`, step is `mon_net_trans.dequeue` (monitor unchanged), consistency via `consistentInstrumentation_replace` |
| `mon_type_dequeuing` | "By inversion, we infer the same shape…" | `CommCorrespondence.mon_dequeue_network_dequeue_norec`: generalise-then-`cases` on `mon_net_trans` (`ofmon_label` cannot unify with `τ_dequeue` directly; `comm` pruned by `simp`), same transfer as forward |
| Forward/backward `comm` | Dequeue case + comm case using `type-send-mon-send` (`STMon-IntC`) and `live-hd-net-enqueue-mon-enqueue` (liveness + half-duplex by contradiction) | `CommCorrespondence.network_comm_mon_comm_norec` / `mon_comm_network_comm_norec`: send side via `monitor_fold_aux_out_aux_norec` once sender absorption is known; receive side (and sender absorption) via `mon_reject_implies_nodrain_norec` + `no_deep_drain_no_output_liveness_hd_norec` contradicting `output_live_persistent` / `IsHalfDuplex.star`; backward pins the monitor target with `mon_tr_yes_target_unique` |
| Recursion unfolding | `unfold(T)` lemma + `STMon-Rec` | `st_trans.tRec` / `mon_tr_yes_*` unfold arms + `UnfoldStar`/`HNF`/`spine` theory; `NoRec` proofs prune `tRec` by `cases hNR` |
| Main theorem case analysis | `dequeue` LR, `dequeue` RL, `comm` LR, `comm` RL | `monitor_soundness_norec`: `cases μ₁`/`cases μ₂`; non-`τ` labels `exfalso` via `is_internal_*`; `τ_dequeue`/`τ_comm` via the four lemmas above (`network_dequeue_mon_dequeue_norec`, `network_comm_mon_comm_norec`, `mon_dequeue_network_dequeue_norec`, `mon_comm_network_comm_norec`) |
| Scope | All closed guarded types | `NoRec` + `WellFormed` + `RolesPresent` + `NoSelf` + output-live + half-duplex + `consistentInstrumentation N = some MN`; termination via `networkBudget` (`noInfiniteInternalPath_of_NoRec`, `norec_live_infinite_vacuous`, `exists_stuck_reachable_of_NoRec`) |

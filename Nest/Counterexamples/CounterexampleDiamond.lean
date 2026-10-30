import Nest.SessionUtils

/-!
# Counterexample: single-step acceptability diamond is false as stated.

Certified witness against `sw_diamond_accept` (`Nest.StuckWitness`):
a `p`-free `st_trans` step need NOT preserve `Exist`-acceptability backwards,
because the prefix rule `pfxInt` demands the side condition `hno`
(`p` is no branch's sender) over ALL branches — not just the taken step.

Concrete instance: `T0 = intC [("p","a","sa",tEnd), ("r","b","sb",B0)]`
with `B0 = extC "p" [("l","s",tEnd)]`.
- Step: `out "r" "b" "sb"` to `B0` (`st_trans.intC`), `p`-free (`"r" ≠ "p"`).
- Acceptability at target: `B0` yes-receives `("p","l","s")` by base-`extC`.
- No derivation at source: `base` is impossible by shape/tag mismatch;
  `pfxInt` needs `hno`, refuted by the lurking `("p",..)` branch
  (`"p" ≠ "p"` is absurd); `pfxExt`/`unfold` are impossible by head shape.

Nothing here depends on maximality, determinism, or the old rigid
definitions: only `st_trans.intC`, base-`extC`, constructor-shape inversion,
and the `hno` side condition — all valid under maximal semantics.

This file is evidence only (not imported by `Nest.lean`); it imports only
`Nest.SessionUtils`, never `BadStuff`/`Proofs`/`StuckWitness`/`NewStuckWitness`.
-/

/-- Target type: offers the distinguished input by base. -/
private def CxD_B0 : SessionType :=
  SessionType.externalChoice "p" [("l", "s", SessionType.tEnd)]

/-- Source type: internal choice with a lurking `p`-sender branch. -/
private def CxD_T0 : SessionType :=
  SessionType.internalChoice [("p", "a", "sa", SessionType.tEnd),
    ("r", "b", "sb", CxD_B0)]

/-- The step: `out "r" "b" "sb"` selects the live branch. -/
private lemma CxD_step : st_trans CxD_T0 (st_label.out "r" "b" "sb") CxD_B0 := by
  unfold CxD_T0
  apply st_trans.intC
  simp

/-- The step is `p`-free: `st_label.involves` (local to `Nest.StuckWitness`)
    unfolds on `out` to sender equality, i.e. `"r" = "p"` here — false. -/
private lemma CxD_free : ¬ ("r" = "p") := by
  decide

/-- The target accepts the distinguished receive (base-`extC`). -/
private lemma CxD_acc :
    ∃ T1', mon_tr_yes_exist CxD_B0 (ext_tag.recv "p" "l" "s") T1' := by
  refine ⟨SessionType.tEnd,
    mon_tr_yes_exist.base (mon_tr_yes_base.extC (by decide) ?_)⟩
  exact List.mem_cons.mpr (Or.inl rfl)

/-- The source admits no existential derivation: `base` by shape/tag
    mismatch; `pfxInt` by `hno` against the lurking `p`-branch;
    `pfxExt`/`unfold` by head-shape mismatch (all auto-closed). -/
theorem CxD_diamond_false :
    ¬ ∃ T1, mon_tr_yes_exist CxD_T0 (ext_tag.recv "p" "l" "s") T1 := by
  rintro ⟨T1, h⟩
  unfold CxD_T0 at h
  cases h with
  | base hb => cases hb
  | @pfxInt branches kept q lab S T' hne hno hkept hall hNodup hkey =>
    exact (hno "p" "a" "sa" SessionType.tEnd (by simp)) rfl

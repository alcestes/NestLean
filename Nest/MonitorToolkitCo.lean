import Nest.MonitorLTSCo

open Cslib
open Cslib.LTS

set_option linter.unusedVariables false

/-! # MonitorToolkitCo: coinductive instrumentation bridge (relational).

Coinductive twins of the consistent-instrumentation bridge lemmas
(`mem_consistentInstrumentation`, `consistentInstrumentation_inv_mem`,
`consistentInstrumentation_filter`, `consistentInstrumentation_replace` in
`Nest/MonitorToolkit.lean`): same statements and proofs, with the
relational `monitor_fold_val_partial_co` and `consistentInstrumentation_co`
in place of the finite versions. No functionalization is used.
-/


/-- Inversion of coinductive consistent instrumentation. -/
lemma consistentInstrumentation_inv_mem_co {N : Network} {r : Role} {stq : SessionTypeWithQueue} {M : SessionType}
    {MN : MonitoredNetwork} (hmem : (r, (stq, M)) ∈ MN) (hCons : consistentInstrumentation_co N = some MN) :
    (r, stq) ∈ N ∧ monitor_fold_val_partial_co stq = some M := by
  induction N generalizing MN with
  | nil =>
    simp [consistentInstrumentation_co] at hCons
    rw [hCons] at hmem
    simp at hmem
  | cons hd tl ih =>
    rcases hd with ⟨r0, stq0⟩
    rw [consistentInstrumentation_co] at hCons
    cases h_e : monitor_fold_val_partial_co stq0 with
    | none => simp [h_e] at hCons
    | some M0 =>
      cases h_c : consistentInstrumentation_co tl with
      | none => simp [h_e, h_c] at hCons
      | some MNtl =>
        rw [h_e, h_c] at hCons
        injection hCons with hMN_eq
        rw [← hMN_eq] at hmem
        simp at hmem
        rcases hmem with (⟨rfl, ⟨rfl, rfl⟩⟩ | htl)
        · exact ⟨by simp, h_e⟩
        · rcases ih htl h_c with ⟨hmem', hev⟩
          exact ⟨by simpa using (Or.inr hmem'), hev⟩

/-- A successful relational partial fold agrees with the relational queue fold.
    The `choose` witness is identified with `M` by option injectivity; no
    uniqueness of targets is needed. -/
theorem monitor_fold_val_partial_co_sound {stq : SessionTypeWithQueue} {M : SessionType}
    (h : monitor_fold_val_partial_co stq = some M) : monitor_fold_co stq M := by
  unfold monitor_fold_val_partial_co at h
  split at h
  · rename_i hEx
    obtain rfl := Option.some_inj.mp h
    exact Classical.choose_spec hEx
  · cases h

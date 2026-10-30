import Nest.SessionUtils
import Nest.StuckWitness
import Nest.MonitorToolkit
import Nest.NoRec.CommCorrespondence
import Nest.NoRec.NoRecEncoder

/-!
# MonitorSoundnessNoRec: NoRec monitor soundness.

If `N` is recursion-free, well-formed, output-live, and half-duplex (no self-sends,
all roles present), then `N` is internally bisimilar to its consistent instrumentation.
-/

section MonitorSoundness
/-- NoRec monitor soundness: if `N` is recursion-free, well-formed,
    output-live, and half-duplex (no self-sends, all roles present), then
    `N` is internally bisimilar to its consistent instrumentation. The
    relation is consistency + `τ*`-reachability from `N`; invariants
    transfer along the star from the root, and each internal step is matched
    by the four correspondence lemmas above. -/
theorem monitor_soundness_norec {MN : MonitoredNetwork} (N : Network)
    (hNR : N.NoRec) (hwf : N.WellFormed)
    (hRP : N.RolesPresent) (hNS : N.NoSelf)
    (h_output_live : IsOutputLiveNetwork N)
    (h_half_duplex : IsHalfDuplex N)
    (hCons : consistentInstrumentation N = some MN) :
    InternallyBisimilar N MN := by
  let R : Network → MonitoredNetwork → Prop :=
    fun N' MN' => consistentInstrumentation N' = some MN' ∧ net_trans_star N N'
  have hR0 : R N MN := ⟨hCons, net_trans_star.refl _⟩
  refine ⟨R, hR0, ?_⟩
  rintro N' MN' ⟨hCons', h_star⟩ μ₁ hIntLbl₁
  have hNR' : N'.NoRec := net_trans_star_preserves_norec h_star hNR
  have hWF' : N'.WellFormed := net_trans_preserves_well_formed hwf h_star
  have hRP' : N'.RolesPresent := net_trans_star_preserves_roles_present h_star hRP
  have hNS' : N'.NoSelf := net_trans_star_preserves_no_self h_star hNS
  have hHD' : IsHalfDuplex N' := h_half_duplex.star h_star
  have hLive' : IsOutputLiveNetwork N' := output_live_persistent hwf h_output_live h_star
  constructor
  · intro N'' hN'_tr
    cases μ₁ with
    | io_send _ _ _ _ => exfalso; exact hIntLbl₁
    | io_recv _ _ _ _ => exfalso; exact hIntLbl₁
    | τ_dequeue r p lab S =>
      obtain ⟨MN'', hStep, hCons''⟩ :=
        network_dequeue_mon_dequeue_norec hNR' hWF' hCons' hN'_tr
      have hInt : is_internal_net_label (net_label.τ_dequeue r p lab S) := by
        simp [is_internal_net_label]
      have h_star' : net_trans_star N N'' :=
        net_trans_star.trans h_star (net_trans_star.step hInt hN'_tr (net_trans_star.refl _))
      exact ⟨MN'', mon_net_label.τ_dequeue r p lab S, by simp [is_internal_mon_net_label],
        rfl, hStep, ⟨hCons'', h_star'⟩⟩
    | τ_comm p q lab S =>
      obtain ⟨MN'', hStep, hCons''⟩ :=
        network_comm_mon_comm_norec hNR' hWF' hRP' hNS' hHD' hLive' hCons' hN'_tr
      have hInt : is_internal_net_label (net_label.τ_comm p q lab S) := by
        simp [is_internal_net_label]
      have h_star' : net_trans_star N N'' :=
        net_trans_star.trans h_star (net_trans_star.step hInt hN'_tr (net_trans_star.refl _))
      exact ⟨MN'', mon_net_label.τ_comm p q lab S, by simp [is_internal_mon_net_label],
        rfl, hStep, ⟨hCons'', h_star'⟩⟩
  · intro M μ₂ hIntLbl₂ hMN'_tr
    cases μ₂ with
    | io_yes_send _ _ _ _ => exfalso; exact hIntLbl₂
    | io_yes_recv _ _ _ _ => exfalso; exact hIntLbl₂
    | io_no_out _ _ _ _ => exfalso; exact hIntLbl₂
    | io_no_inp _ _ _ _ => exfalso; exact hIntLbl₂
    | τ_dequeue r p lab S =>
      obtain ⟨N'', hStep, hCons''⟩ :=
        mon_dequeue_network_dequeue_norec hNR' hWF' hCons' hMN'_tr
      have hInt : is_internal_net_label (net_label.τ_dequeue r p lab S) := by
        simp [is_internal_net_label]
      have h_star' : net_trans_star N N'' :=
        net_trans_star.trans h_star (net_trans_star.step hInt hStep (net_trans_star.refl _))
      exact ⟨N'', net_label.τ_dequeue r p lab S, by simp [is_internal_net_label],
        rfl, hStep, ⟨hCons'', h_star'⟩⟩
    | τ_comm p q lab S =>
      obtain ⟨N'', hStep, hCons''⟩ :=
        mon_comm_network_comm_norec hNR' hWF' hRP' hNS' hHD' hLive' hCons' hMN'_tr
      have hInt : is_internal_net_label (net_label.τ_comm p q lab S) := by
        simp [is_internal_net_label]
      have h_star' : net_trans_star N N'' :=
        net_trans_star.trans h_star (net_trans_star.step hInt hStep (net_trans_star.refl _))
      exact ⟨N'', net_label.τ_comm p q lab S, by simp [is_internal_net_label],
        rfl, hStep, ⟨hCons'', h_star'⟩⟩
end MonitorSoundness

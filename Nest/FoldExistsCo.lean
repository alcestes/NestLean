import Nest.MonitorCoRel
import Nest.MonitorCoBase
import Nest.MonitorLTS
import Nest.SessionUtils

open Cslib
open Cslib.LTS

set_option linter.unusedVariables false

/-! # FoldExistsCo: finite Fold existence from existential acceptance.

Relational (non-executable) existence of Fold derivations: every eligible
observation of a well-formed type admits a finite `fmon` derivation,
building on the `prune_step_wf`, `unfoldstar_prune`, `Ex_send_base`, and
`base_unfoldstar_lift` helpers in `Nest/MonitorCoFun.lean`, with
`mon_tr_yes` conclusions restated as `fmon []` derivations.

Credit: Jules Jacobs <jules.jacobs@inf.ethz.ch> and
Nate Foster <nate.foster@epfl.ch> and Kristýna Petrlíková <auburn@kam.mff.cuni.cz>.
-/

/-- Closed recursive session syntax has a finite closure under branch descent
    and unfolding. -/
theorem finite_traversal {T : SessionType} (closed : T.IsClosed) :
    {U | Relation.ReflTransGen PruneStep T U}.Finite := by
  have envClosed : env_closed [] := by intro x value member; cases member
  have covered : ∀ x ∈ T.fv, elookup [] x ≠ none := by
    intro x member
    simp [SessionType.IsClosed] at closed
    simp [closed] at member
  have root : T ∈ traversalNodes [] T := by
    simpa [ssubst_nil] using traversalNodes_root T []
  have closedNodes {U V : SessionType} (member : U ∈ traversalNodes [] T)
      (step : PruneStep U V) : V ∈ traversalNodes [] T := by
    rcases traversalNodes_step T [] envClosed covered member step with next | ⟨x, absent⟩
    · exact next
    · cases absent
  apply (List.finite_toSet (traversalNodes [] T)).subset
  intro U reachable
  induction reachable with
  | refl => exact root
  | tail reach step ih => exact closedNodes ih step

theorem pfx_build {G H q lab S} (hW : H.WellFormed) (hNF : IsHeadNF H)
    (hEx : Ex H (.recv q lab S)) (hNoBase : ∀ V, ¬ mon_tr_yes_base H (.recv q lab S) V)
    (hKids : ∀ C, PruneStep H C → Ex C (.recv q lab S) → ∃ V, fchild G C (.recv q lab S) V) :
    ∃ V, fmon G H (.recv q lab S) V := by
  obtain ⟨V0,hEx⟩ := hEx
  cases hEx with
  | base hb => exact (hNoBase _ hb).elim
  | @pfxInt bs kept0 _ _ _ _ hne hno heq hall hnd0 hkey =>
      obtain ⟨kept,hk⟩ := KRint_build (fun T0 => Ex T0 (.recv q lab S))
        (fun T0 T1 => fchild G T0 (.recv q lab S) T1) bs
        (fun r l s T0 hin hE => hKids T0 (.intC hin) hE)
      have hnd3 := SessionType.NoDupl.triple_nodup_of_internalChoice hW.1
      refine ⟨.internalChoice kept,.fm_pfxInt hne.1 ?_ hno ?_ ?_ ?_ ?_ (KRint_sublist3 hk)⟩
      · obtain ⟨⟨r,l,s,T1⟩,h1⟩ := List.exists_mem_of_ne_nil kept0 hne.2
        obtain ⟨T0,h0⟩ := hkey r l s T1 h1
        obtain ⟨T2,h2,_⟩ := KRint_cover hk h0 ⟨T1,hall T0 T1 r l s h0 h1⟩
        exact List.ne_nil_of_mem h2
      · intro T0 T1 r l s h0 h1
        obtain ⟨T0',h0',_,hp⟩ := KRint_kept_mem hk h1
        have heq := unique_target_of_nodup_int hnd3 h0 h0'
        subst T0'
        exact hp
      · exact (KRint_sublist2 hk).nodup (nodup_int_key_of_wf hW)
      · intro r l s T1 h1
        obtain ⟨T0,h0,hE,_⟩ := KRint_kept_mem hk h1
        exact ⟨T0,h0,hE⟩
      · intro r l s T0 h0 hE
        obtain ⟨T1,h1,_⟩ := KRint_cover hk h0 hE
        exact ⟨T1,h1⟩
  | @pfxExt p bs kept0 _ _ _ _ hne hneq heq hall hnd0 hkey =>
      obtain ⟨kept,hk⟩ := KRext_build (fun T0 => Ex T0 (.recv q lab S))
        (fun T0 T1 => fchild G T0 (.recv q lab S) T1) bs
        (fun l s T0 hin hE => hKids T0 (.extC hin) hE)
      have hnd2 := nodup_ext_key2_of_wf hW
      refine ⟨.externalChoice p kept,.fm_pfxExt hne.1 ?_ hneq ?_ ?_ ?_ ?_ (KRext_sublist2 hk)⟩
      · obtain ⟨⟨l,s,T1⟩,h1⟩ := List.exists_mem_of_ne_nil kept0 hne.2
        obtain ⟨T0,h0⟩ := hkey l s T1 h1
        obtain ⟨T2,h2,_⟩ := KRext_cover hk h0 ⟨T1,hall T0 T1 l s h0 h1⟩
        exact List.ne_nil_of_mem h2
      · intro T0 T1 l s h0 h1
        obtain ⟨T0',h0',_,hp⟩ := KRext_kept_mem hk h1
        have heq := unique_target_of_nodup_ext hnd2 h0 h0'
        subst T0'
        exact hp
      · exact (KRext_sublist1 hk).nodup (nodup_ext_key_of_wf hW)
      · intro l s T1 h1
        obtain ⟨T0,h0,hE,_⟩ := KRext_kept_mem hk h1
        exact ⟨T0,h0,hE⟩
      · intro l s T0 h0 hE
        obtain ⟨T1,h1,_⟩ := KRext_cover hk h0 hE
        exact ⟨T1,h1⟩
  | unfold h => exact hNF.elim

private lemma child_of_frame {g G C}
    (hF : C ∉ G.map Prod.fst → Ex C g → ∃ V, fmon G C g V)
    (hE : Ex C g) : ∃ V, fchild G C g V := by
  classical
  by_cases hin : C ∈ G.map Prod.fst
  · obtain ⟨⟨C',u⟩,hin,heq⟩ := List.mem_map.mp hin
    change C' = C at heq
    subst C'
    exact ⟨.tVar u,.fc_fold hin⟩
  · obtain ⟨V,hV⟩ := hF hin hE
    exact ⟨V,.fc_go hin hV⟩

private lemma choice_frame {G T g} (hC : IsChoice T) (hW : T.WellFormed) (hE : Ex T g)
    (hKids : ∀ C, PruneStep T C → C ∉ G.map Prod.fst → Ex C g → ∃ V, fmon G C g V) :
    ∃ V, fmon G T g V := by
  classical
  by_cases hb : ∃ V, mon_tr_yes_base T g V
  · obtain ⟨V,hb⟩ := hb
    exact ⟨V,.fm_base hb⟩
  · cases g with
    | send p l s => exact (hb (Ex_send_base hE)).elim
    | recv q lab S =>
        refine pfx_build hW ?_ hE (fun V h => hb ⟨V,h⟩) ?_
        · cases T <;> simp_all [IsChoice, IsHeadNF]
        · intro C hs hEC
          exact child_of_frame (hKids C hs) hEC

private def Covers (R : SessionType → Prop) (n : Nat) (G : FCtx) : Prop :=
  ∃ L : Finset SessionType, L.card ≤ n ∧ ∀ U, R U → U ∉ G.map Prod.fst → U ∈ L

private lemma preserve_reach {R : SessionType → Prop}
    (step : ∀ T U, R T → PruneStep T U → R U) {T U}
    (hR : R T) (path : Relation.ReflTransGen PruneStep T U) : R U := by
  induction path with
  | refl => exact hR
  | tail hs hu ih => exact step _ _ ih hu

private lemma build_frame (R : SessionType → Prop)
    (wf : ∀ T, R T → T.WellFormed)
    (step : ∀ T U, R T → PruneStep T U → R U)
    (g : ext_tag) (n : Nat) :
    ∀ G T, Covers R n G → R T → T ∉ G.map Prod.fst → Ex T g → ∃ V, fmon G T g V := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ihn =>
      intro G
      have go : ∀ k T, sizeOf T = k → Covers R n G → R T → T ∉ G.map Prod.fst →
          Ex T g → ∃ V, fmon G T g V := by
        intro k
        induction k using Nat.strong_induction_on with
        | h k ihT =>
            intro T hsize hCov hR hFresh hE
            have hW := wf T hR
            cases T with
            | internalChoice bs =>
                apply choice_frame (T := .internalChoice bs) trivial hW hE
                intro C hs hFreshC hEC
                cases hs with
                | intC hm =>
                    have hsz := sizeOf_SessionType_lt_sizeOf_internalChoice hm
                    rw [hsize] at hsz
                    exact ihT _ hsz _ rfl hCov (step _ _ hR (.intC hm)) hFreshC hEC
            | externalChoice p bs =>
                apply choice_frame (T := .externalChoice p bs) trivial hW hE
                intro C hs hFreshC hEC
                cases hs with
                | extC hm =>
                    have hsz := sizeOf_SessionType_lt_sizeOf_externalChoice (p := p) hm
                    rw [hsize] at hsz
                    exact ihT _ hsz _ rfl hCov (step _ _ hR (.extC hm)) hFreshC hEC
            | tEnd =>
                obtain ⟨V,hV⟩ := hE
                cases hV with | base hb => cases hb
            | tVar X =>
                obtain ⟨V,hV⟩ := hE
                cases hV with | base hb => cases hb
            | tRec X B =>
                by_cases hb : ∃ V, mon_tr_yes_base (.tRec X B) g V
                · obtain ⟨V,hb⟩ := hb
                  exact ⟨V,.fm_base hb⟩
                · obtain ⟨H,hS,hNF⟩ := unfoldStar_normal_exists (.tRec X B) hW.2.2 hW.2.1
                  obtain ⟨L,hL,hcov⟩ := hCov
                  have hmem := hcov _ hR hFresh
                  have hlt := Finset.card_erase_lt_of_mem hmem
                  let G' : FCtx := (.tRec X B, fvar G.length) :: G
                  have hCov' : Covers R (L.erase (.tRec X B)).card G' := by
                    refine ⟨L.erase (.tRec X B),le_rfl,?_⟩
                    intro U hU hnU
                    apply Finset.mem_erase.mpr
                    constructor
                    · intro heq
                      subst U
                      exact hnU (by simp [G'])
                    · exact hcov U hU (fun hm => hnU (by simp [G',hm]))
                  have hRH := preserve_reach step hR (unfoldstar_prune hS)
                  have hWH := wf H hRH
                  have hEH := (Ex_unfoldstar hS).mp hE
                  have hBody : ∃ V, fmon G' H g V := by
                    cases g with
                    | send p l s =>
                        obtain ⟨V,hbase⟩ := Ex_send_base hEH
                        exact (hb ⟨V,base_unfoldstar_lift hS hbase⟩).elim
                    | recv q lab S =>
                        apply pfx_build hWH hNF hEH (fun V hbase => hb ⟨V,base_unfoldstar_lift hS hbase⟩)
                        intro C hs hEC
                        apply child_of_frame ?_ hEC
                        intro hnC hEC
                        exact ihn _ (by omega) G' C hCov' (step H C hRH hs) hnC hEC
                  obtain ⟨V,hV⟩ := hBody
                  exact ⟨mkRec (fvar G.length) V,.fm_rec hS hNF hV⟩
      intro T
      exact go (sizeOf T) T rfl

theorem fmon_exists_of_finite {T g} (hW : T.WellFormed)
    (hFin : {U | Relation.ReflTransGen PruneStep T U}.Finite)
    (hE : Ex T g) : ∃ V, fmon [] T g V := by
  let R := fun U => Relation.ReflTransGen PruneStep T U
  have wf : ∀ U, R U → U.WellFormed := by
    intro U path
    induction path with
    | refl => exact hW
    | tail path next ih => exact prune_step_wf next ih
  apply build_frame R wf (fun _ _ path next => path.tail next) g hFin.toFinset.card [] T
  · refine ⟨hFin.toFinset,le_rfl,?_⟩
    intro U hU _
    exact hFin.mem_toFinset.mpr hU
  · exact .refl
  · simp
  · exact hE

theorem fmon_exists {T g} (hW : T.WellFormed) (hE : Ex T g) : ∃ V, fmon [] T g V :=
  fmon_exists_of_finite hW (finite_traversal hW.2.1) hE

import Nest.SessionUtils
import Nest.SessionAdequacy
import Nest.Tests.PrunableTest
import Nest.Drainability
import Nest.Examples.ProofUtils
import Nest.MonitorLTSCo
import Nest.MonitorCoFun

namespace Firewall

/- Session types from the NEST P4 testbed:
   `NEST/nest/nest_scala/src/main/scala/examples/04_firewall.scala`
   (Scala package `firewall`; file `04_firewall.scala` maps to this
   module since Lean module names may not start with a digit).
   Translated below are the two `lst_*` local session types
   (`lst_ClientInt`, `lst_ClientExt`). Switch setup, IP rules, port
   checks and monitor wiring from `setup` are not session types and
   are not translated. Translation conventions: `IntChoice` branches
   become `internalChoice` branches `(agent, label, sort, cont)`;
   `ExtChoice` branches become `externalChoice` branches
   `(label, sort, cont)`; `Rec`/`Var`/`End` become `tRec`/`tVar`/`tEnd`.
   Agents become roles, labels stay labels. The Scala types carry no
   payload sorts, so every branch uses the placeholder sort `"unit"`. -/

/-- `lst_ClientInt`. -/
def ClientInt : SessionType :=
  SessionType.tRec "Outgoing"
    (SessionType.internalChoice
      [("ClientExt", "Request", "unit",
        SessionType.externalChoice "ClientExt"
          [("Response", "unit", SessionType.tVar "Outgoing")]),
       ("ClientExt", "Terminate", "unit",
        SessionType.tRec "Incoming"
          (SessionType.externalChoice "ClientExt"
            [("Request", "unit",
              SessionType.internalChoice
                [("ClientExt", "Response", "unit",
                  SessionType.tVar "Incoming")]),
             ("Terminate", "unit", SessionType.tEnd)]))])

/-- `lst_ClientExt`. -/
def ClientExt : SessionType :=
  SessionType.tRec "Outgoing"
    (SessionType.externalChoice "ClientInt"
      [("Request", "unit",
        SessionType.internalChoice
          [("ClientInt", "Response", "unit",
            SessionType.tVar "Outgoing")]),
       ("Terminate", "unit",
        SessionType.tRec "Incoming"
          (SessionType.internalChoice
            [("ClientInt", "Request", "unit",
              SessionType.externalChoice "ClientInt"
                [("Response", "unit", SessionType.tVar "Incoming")]),
             ("ClientInt", "Terminate", "unit", SessionType.tEnd)]))])

-- `lst_ClientInt` is deeply adequate (mirror `FwT` carries the proof).
/-- External offer by `ClientExt`: `(Response, unit)` looping on `Outgoing` (`ClientInt`
   mirror). -/
def FwT1 : SessionType :=
  SessionType.externalChoice "ClientExt" [("Response", "unit", SessionType.tVar "Outgoing")]
/-- Internal choice: `(ClientExt, Response, unit)` looping on `Incoming` (`ClientInt` mirror). -/
def FwT3 : SessionType :=
  SessionType.internalChoice [("ClientExt", "Response", "unit", SessionType.tVar "Incoming")]
/-- External offer by `ClientExt`: `(Request, unit)` continuing as `FwT3`; `(Terminate, unit)`
   ending in `tEnd` (`ClientInt` mirror). -/
def FwBin : SessionType :=
  SessionType.externalChoice "ClientExt"
    [("Request", "unit", FwT3),
     ("Terminate", "unit", SessionType.tEnd)]
/-- Internal choice: `(ClientExt, Request, unit)` continuing as `FwT1`; `(ClientExt, Terminate,
   unit)` continuing into `tRec` (`ClientInt` mirror). -/
def FwBout : SessionType :=
  SessionType.internalChoice
    [("ClientExt", "Request", "unit", FwT1),
     ("ClientExt", "Terminate", "unit", SessionType.tRec "Incoming" FwBin)]
/-- Recursive type: loop on `Outgoing` with body `FwBout` (`ClientInt` mirror). -/
def FwT := SessionType.tRec "Outgoing" FwBout
/-- Recursive type: loop on `Incoming` with body `FwBin` (`ClientInt` mirror). -/
def FwI := SessionType.tRec "Incoming" FwBin
/-- External offer by `ClientExt`: `(Response, unit)` continuing as `FwT` (`ClientInt` mirror). -/
def FwT1c : SessionType :=
  SessionType.externalChoice "ClientExt" [("Response", "unit", FwT)]
/-- Internal choice: `(ClientExt, Response, unit)` continuing as `FwI` (`ClientInt` mirror). -/
def FwT3c : SessionType :=
  SessionType.internalChoice [("ClientExt", "Response", "unit", FwI)]
/-- External offer by `ClientExt`: `(Request, unit)` continuing as `FwT3c`; `(Terminate, unit)`
   ending in `tEnd` (`ClientInt` mirror). -/
def FwSin : SessionType :=
  SessionType.externalChoice "ClientExt" [("Request", "unit", FwT3c), ("Terminate", "unit", SessionType.tEnd)]
/-- Internal choice: `(ClientExt, Request, unit)` continuing as `FwT1c`; `(ClientExt, Terminate,
   unit)` continuing as `FwI` (`ClientInt` mirror). -/
def FwSout : SessionType :=
  SessionType.internalChoice [("ClientExt", "Request", "unit", FwT1c), ("ClientExt", "Terminate", "unit", FwI)]

/-- Grafting equation: substituting `(SessionType.tRec "Outgoing" FwBout)` for `Outgoing` in
   `FwBout` yields `FwSout`. -/
theorem FwSout_subst :
    substSessionType FwBout "Outgoing" (SessionType.tRec "Outgoing" FwBout) = FwSout := rfl
/-- Grafting equation: substituting `(SessionType.tRec "Incoming" FwBin)` for `Incoming` in
   `FwBin` yields `FwSin`. -/
theorem FwSin_subst :
    substSessionType FwBin "Incoming" (SessionType.tRec "Incoming" FwBin) = FwSin := rfl
/-- Freshness: `FwI` is distinct from the listed states. -/
theorem FwI_fresh : FwI ∉ [FwT] := by
  intro hcon
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hcon
  injection hcon with hXY _
  exact absurd hXY (by decide)
/-- The prune `Has` check for (`ClientExt`, `Request`, `unit`) on `FwT1c` is `false` (absent
   from the type). -/
theorem Fw_has_T1c_Req_false :
    pruneFirstInputDeepHas "ClientExt" "Request" "unit" FwT1c = false := by decide
/-- The prune `Has` check for (`ClientExt`, `Response`, `unit`) on `FwI` is `false` (absent from
   the type). -/
theorem Fw_has_I_Resp_false :
    pruneFirstInputDeepHas "ClientExt" "Response" "unit" FwI = false := by decide
/-- The prune `Has` check for (`ClientExt`, `Terminate`, `unit`) on `FwT1c` is `false` (absent
   from the type). -/
theorem Fw_has_T1c_Term_false :
    pruneFirstInputDeepHas "ClientExt" "Terminate" "unit" FwT1c = false := by decide

/-- One-message prunability of `FwT1c` for (`ClientExt`, `Response`, `unit`). -/
theorem FA_T1c_Resp : PrunableOneMsg "ClientExt" "Response" "unit" FwT1c :=
  prunable_one_msg_extC_owner "ClientExt" _ "Response" "unit"
/-- One-message prunability of `FwSin` for (`ClientExt`, `Request`, `unit`). -/
theorem FA_Sin_Req : PrunableOneMsg "ClientExt" "Request" "unit" FwSin :=
  prunable_one_msg_extC_owner "ClientExt" _ "Request" "unit"
/-- One-message prunability of `FwSin` for (`ClientExt`, `Response`, `unit`). -/
theorem FA_Sin_Resp : PrunableOneMsg "ClientExt" "Response" "unit" FwSin :=
  prunable_one_msg_extC_owner "ClientExt" _ "Response" "unit"
/-- One-message prunability of `FwSin` for (`ClientExt`, `Terminate`, `unit`). -/
theorem FA_Sin_Term : PrunableOneMsg "ClientExt" "Terminate" "unit" FwSin :=
  prunable_one_msg_extC_owner "ClientExt" _ "Terminate" "unit"
/-- One-message prunability of `FwI` for (`ClientExt`, `Request`, `unit`). -/
theorem FA_I_Req : PrunableOneMsg "ClientExt" "Request" "unit" FwI :=
  prunable_one_msg_trec_of_succ "ClientExt" "Request" "unit" FA_Sin_Req
/-- One-message prunability of `FwI` for (`ClientExt`, `Response`, `unit`). -/
theorem FA_I_Resp : PrunableOneMsg "ClientExt" "Response" "unit" FwI :=
  prunable_one_msg_trec_of_succ "ClientExt" "Response" "unit" FA_Sin_Resp
/-- One-message prunability of `FwI` for (`ClientExt`, `Terminate`, `unit`). -/
theorem FA_I_Term : PrunableOneMsg "ClientExt" "Terminate" "unit" FwI :=
  prunable_one_msg_trec_of_succ "ClientExt" "Terminate" "unit" FA_Sin_Term
/-- One-message prunability of `FwSout` for (`ClientExt`, `Request`, `unit`). -/
theorem FA_S_Req : PrunableOneMsg "ClientExt" "Request" "unit" FwSout := by
  apply prunable_one_msg_intC_of_step _ "ClientExt" "Request" "unit"
  intro V hS
  cases hS with
  | @intC _ x hmem hHas =>
    obtain ⟨r, l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · rw [Fw_has_T1c_Req_false] at hHas
      cases hHas
    · exact FA_I_Req
/-- One-message prunability of `FwSout` for (`ClientExt`, `Response`, `unit`). -/
theorem FA_S_Resp : PrunableOneMsg "ClientExt" "Response" "unit" FwSout := by
  apply prunable_one_msg_intC_of_step _ "ClientExt" "Response" "unit"
  intro V hS
  cases hS with
  | @intC _ x hmem hHas =>
    obtain ⟨r, l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · exact FA_T1c_Resp
    · rw [Fw_has_I_Resp_false] at hHas
      cases hHas
/-- One-message prunability of `FwSout` for (`ClientExt`, `Terminate`, `unit`). -/
theorem FA_S_Term : PrunableOneMsg "ClientExt" "Terminate" "unit" FwSout := by
  apply prunable_one_msg_intC_of_step _ "ClientExt" "Terminate" "unit"
  intro V hS
  cases hS with
  | @intC _ x hmem hHas =>
    obtain ⟨r, l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · rw [Fw_has_T1c_Term_false] at hHas
      cases hHas
    · exact FA_I_Term
/-- One-message prunability of `FwT` for (`ClientExt`, `Request`, `unit`). -/
theorem FA_T_Req : PrunableOneMsg "ClientExt" "Request" "unit" FwT :=
  prunable_one_msg_trec_of_succ "ClientExt" "Request" "unit" FA_S_Req
/-- One-message prunability of `FwT` for (`ClientExt`, `Response`, `unit`). -/
theorem FA_T_Resp : PrunableOneMsg "ClientExt" "Response" "unit" FwT :=
  prunable_one_msg_trec_of_succ "ClientExt" "Response" "unit" FA_S_Resp
/-- One-message prunability of `FwT` for (`ClientExt`, `Terminate`, `unit`). -/
theorem FA_T_Term : PrunableOneMsg "ClientExt" "Terminate" "unit" FwT :=
  prunable_one_msg_trec_of_succ "ClientExt" "Terminate" "unit" FA_S_Term

/-- One-message prunability fact. -/
theorem hfaT_fw : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
    ExposedFrom FwT pm lab0 S0 → PrunableOneMsg pm lab0 S0 FwT := by
  intro pm lab0 S0 hexp
  cases hexp with
  | trec hsub =>
    cases hsub with
    | intC_step hmem hne hsub2 =>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
      rcases hmem with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
      · cases hsub2 with
        | extC_here hmem2 =>
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
          obtain ⟨rfl, rfl, rfl⟩ := hmem2
          exact FA_T_Resp
        | extC_step hne2 hmem2 hsub3 =>
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
          obtain ⟨rfl, rfl, rfl⟩ := hmem2
          cases hsub3
      · cases hsub2 with
        | trec hsub3 =>
          cases hsub3 with
          | extC_here hmem3 =>
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem3
            rcases hmem3 with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
            · exact FA_T_Req
            · exact FA_T_Term
          | extC_step hne3 hmem3 hsub4 =>
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem3
            rcases hmem3 with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
            · cases hsub4 with
              | intC_step hmem5 hne5 hsub6 =>
                simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem5
                obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem5
                cases hsub6
            · cases hsub4

/-- One-message prunability fact. -/
theorem hfaI_fw : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
    ExposedFrom FwI pm lab0 S0 → PrunableOneMsg pm lab0 S0 FwI := by
  intro pm lab0 S0 hexp
  cases hexp with
  | trec hsub =>
    cases hsub with
    | extC_here hmem =>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
      rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · exact FA_I_Req
      · exact FA_I_Term
    | extC_step hne hmem hsub2 =>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
      rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · cases hsub2 with
        | intC_step hmem2 hne2 hsub3 =>
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
          obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem2
          cases hsub3
      · cases hsub2

/-- One-message prunability fact. -/
theorem hfaT1c_fw : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
    ExposedFrom FwT1c pm lab0 S0 → PrunableOneMsg pm lab0 S0 FwT1c := by
  intro pm lab0 S0 hexp
  cases hexp with
  | extC_here hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    exact FA_T1c_Resp
  | extC_step hne hmem hsub =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    apply prunable_one_msg_extC_of_step "ClientExt" _ pm lab0 S0
    intro V hS
    cases hS with
    | @extCQ _ _ x _ hmem' _ =>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem'
      obtain ⟨rfl, rfl, rfl⟩ := hmem'
      exact hfaT_fw _ _ _ hsub

/-- One-message prunability fact. -/
theorem hfaT3c_fw : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
    ExposedFrom FwT3c pm lab0 S0 → PrunableOneMsg pm lab0 S0 FwT3c := by
  intro pm lab0 S0 hexp
  cases hexp with
  | intC_step hmem hne hsub =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
    apply prunable_one_msg_intC_of_step _ pm lab0 S0
    intro V hS
    cases hS with
    | @intC _ x hmem' hHas' =>
      obtain ⟨r, l, s, U⟩ := x
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem'
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem'
      exact hfaI_fw _ _ _ (has_to_exposed _ _ _ _ hHas')

/-- One-message prunability fact. -/
theorem hfaSin_fw : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
    ExposedFrom FwSin pm lab0 S0 → PrunableOneMsg pm lab0 S0 FwSin := by
  intro pm lab0 S0 _
  apply prunable_one_msg_extC_of_step "ClientExt" _ pm lab0 S0
  intro V hS
  cases hS with
  | @extCQ _ _ x _ hmem hHas =>
    obtain ⟨l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact hfaT3c_fw _ _ _ (has_to_exposed _ _ _ _ hHas)
    · exact prunable_one_msg_end _ _ _

/-- One-message prunability fact. -/
theorem hfaS_fw : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
    ExposedFrom FwSout pm lab0 S0 → PrunableOneMsg pm lab0 S0 FwSout := by
  intro pm lab0 S0 _
  apply prunable_one_msg_intC_of_step _ pm lab0 S0
  intro V hS
  cases hS with
  | @intC _ x hmem hHas =>
    obtain ⟨r, l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · exact hfaT1c_fw _ _ _ (has_to_exposed _ _ _ _ hHas)
    · exact hfaI_fw _ _ _ (has_to_exposed _ _ _ _ hHas)

/-- Deep adequacy of `FwT` with empty seen set. -/
theorem FwT_deep : Prunable [] FwT := by
  apply Prunable.trec_new [] "Outgoing" FwBout _ _ hfaT_fw
  · simp
  · rw [FwSout_subst]
    apply Prunable.intC [FwT] _ _ hfaS_fw
    intro x hmem
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with rfl | rfl
    · apply Prunable.extC [FwT] "ClientExt" _ _ hfaT1c_fw
      intro y hmemY
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmemY
      obtain rfl := hmemY
      exact Prunable.trec_seen [FwT] "Outgoing" FwBout
        (List.mem_cons.mpr (Or.inl rfl)) hfaT_fw
    · have hPrunableI : Prunable [FwT] FwI := by
        apply Prunable.trec_new [FwT] "Incoming" FwBin _ _ hfaI_fw
        · exact FwI_fresh
        · rw [FwSin_subst]
          apply Prunable.extC [FwI, FwT] "ClientExt" _ _ hfaSin_fw
          intro z hmemZ
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmemZ
          rcases hmemZ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
          · apply Prunable.intC [FwI, FwT] _ _ hfaT3c_fw
            intro w hmemW
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmemW
            obtain ⟨rfl, rfl, rfl, rfl⟩ := hmemW
            exact Prunable.trec_seen [FwI, FwT] "Incoming" FwBin
              (List.mem_cons.mpr (Or.inl rfl)) hfaI_fw
          · exact Prunable.tEnd [FwI, FwT]
      exact hPrunableI

/-- Definitional unfolding: `FwT` is definitionally the stated type. -/
theorem FwT_eq : FwT = ClientInt := rfl

/-- Deep adequacy of `ClientInt` with empty seen set. -/
theorem ClientInt_deep : Prunable [] ClientInt := by
  rw [← FwT_eq]
  exact FwT_deep

/-- Monitorability of `ClientInt` (finite prune closure). -/
theorem ClientInt_mon : Drainability.Monitorable ClientInt := by
  have hRW : ClientInt = FwT := rfl
  rw [hRW]
  apply Monitorable_of_closed_set FwT
    {FwT, FwSout, FwT1c, FwI, FwSin, FwT3c, SessionType.tEnd,
     SessionType.tVar "Outgoing", SessionType.tVar "Incoming"}
  · simp
  · intro U hU V hStep
    simp only [Finset.mem_insert, Finset.mem_singleton] at hU
    rcases hU with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · cases hStep with
      | trec => rw [FwSout_subst]; simp
    · cases hStep with
      | intC hmem =>
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
        rcases hmem with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · simp
        · simp
    · cases hStep with
      | extC hmem =>
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
        obtain ⟨rfl, rfl, rfl⟩ := hmem
        simp
    · cases hStep with
      | trec => rw [FwSin_subst]; simp
    · cases hStep with
      | extC hmem =>
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
        rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
        · simp
        · simp
    · cases hStep with
      | intC hmem =>
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
        simp
    · cases hStep
    · cases hStep
    · cases hStep

-- `lst_ClientExt` is deeply adequate (mirror `XcT` carries the proof).
/-- Internal choice: `(ClientInt, Response, unit)` looping on `Outgoing` (`ClientExt` mirror). -/
def XcI1 : SessionType :=
  SessionType.internalChoice [("ClientInt", "Response", "unit", SessionType.tVar "Outgoing")]
/-- External offer by `ClientInt`: `(Response, unit)` looping on `Incoming` (`ClientExt`
   mirror). -/
def XcE3 : SessionType :=
  SessionType.externalChoice "ClientInt" [("Response", "unit", SessionType.tVar "Incoming")]
/-- Internal choice: `(ClientInt, Request, unit)` continuing as `XcE3`; `(ClientInt, Terminate,
   unit)` ending in `tEnd` (`ClientExt` mirror). -/
def XcBin : SessionType :=
  SessionType.internalChoice
    [("ClientInt", "Request", "unit", XcE3),
     ("ClientInt", "Terminate", "unit", SessionType.tEnd)]
/-- External offer by `ClientInt`: `(Request, unit)` continuing as `XcI1`; `(Terminate, unit)`
   continuing into `tRec` (`ClientExt` mirror). -/
def XcBout : SessionType :=
  SessionType.externalChoice "ClientInt"
    [("Request", "unit", XcI1),
     ("Terminate", "unit", SessionType.tRec "Incoming" XcBin)]
/-- Recursive type: loop on `Outgoing` with body `XcBout` (`ClientExt` mirror). -/
def XcT := SessionType.tRec "Outgoing" XcBout
/-- Recursive type: loop on `Incoming` with body `XcBin` (`ClientExt` mirror). -/
def XcI := SessionType.tRec "Incoming" XcBin
/-- Internal choice: `(ClientInt, Response, unit)` continuing as `XcT` (`ClientExt` mirror). -/
def XcI1c : SessionType :=
  SessionType.internalChoice [("ClientInt", "Response", "unit", XcT)]
/-- External offer by `ClientInt`: `(Response, unit)` continuing as `XcI` (`ClientExt` mirror). -/
def XcE3c : SessionType :=
  SessionType.externalChoice "ClientInt" [("Response", "unit", XcI)]
/-- Internal choice: `(ClientInt, Request, unit)` continuing as `XcE3c`; `(ClientInt, Terminate,
   unit)` ending in `tEnd` (`ClientExt` mirror). -/
def XcSin : SessionType :=
  SessionType.internalChoice
    [("ClientInt", "Request", "unit", XcE3c),
     ("ClientInt", "Terminate", "unit", SessionType.tEnd)]
/-- External offer by `ClientInt`: `(Request, unit)` continuing as `XcI1c`; `(Terminate, unit)`
   continuing as `XcI` (`ClientExt` mirror). -/
def XcSout : SessionType :=
  SessionType.externalChoice "ClientInt" [("Request", "unit", XcI1c), ("Terminate", "unit", XcI)]

/-- Grafting equation: substituting `(SessionType.tRec "Outgoing" XcBout)` for `Outgoing` in
   `XcBout` yields `XcSout`. -/
theorem XcSout_subst :
    substSessionType XcBout "Outgoing" (SessionType.tRec "Outgoing" XcBout) = XcSout := rfl
/-- Grafting equation: substituting `(SessionType.tRec "Incoming" XcBin)` for `Incoming` in
   `XcBin` yields `XcSin`. -/
theorem XcSin_subst :
    substSessionType XcBin "Incoming" (SessionType.tRec "Incoming" XcBin) = XcSin := rfl
/-- Freshness: `XcI` is distinct from the listed states. -/
theorem XcI_fresh : XcI ∉ [XcT] := by
  intro hcon
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hcon
  injection hcon with hXY _
  exact absurd hXY (by decide)
/-- The prune `Has` check for (`ClientInt`, `Response`, `unit`) on `XcT` is `false` (absent from
   the type). -/
theorem Xc_has_Resp_XcT_false :
    pruneFirstInputDeepHas "ClientInt" "Response" "unit" XcT = false := by decide
/-- The prune `Has` check for (`ClientInt`, `Request`, `unit`) on `SessionType.tEnd` is `false`
   (absent from the type). -/
theorem Xc_has_End_Req_false :
    pruneFirstInputDeepHas "ClientInt" "Request" "unit" SessionType.tEnd = false := by decide
/-- The prune `Has` check for (`ClientInt`, `Terminate`, `unit`) on `SessionType.tEnd` is
   `false` (absent from the type). -/
theorem Xc_has_End_Term_false :
    pruneFirstInputDeepHas "ClientInt" "Terminate" "unit" SessionType.tEnd = false := by decide
/-- The prune `Has` check for (`ClientInt`, `Response`, `unit`) on `SessionType.tEnd` is `false`
   (absent from the type). -/
theorem Xc_has_End_Resp_false :
    pruneFirstInputDeepHas "ClientInt" "Response" "unit" SessionType.tEnd = false := by decide
/-- The prune `Has` check for (`ClientInt`, `Request`, `unit`) on `XcE3c` is `false` (absent
   from the type). -/
theorem Xc_has_Req_XcE3c_false :
    pruneFirstInputDeepHas "ClientInt" "Request" "unit" XcE3c = false := by decide
/-- The prune `Has` check for (`ClientInt`, `Terminate`, `unit`) on `XcE3c` is `false` (absent
   from the type). -/
theorem Xc_has_Term_XcE3c_false :
    pruneFirstInputDeepHas "ClientInt" "Terminate" "unit" XcE3c = false := by decide

/-- One-message prunability of `XcSout` for (`ClientInt`, `Request`, `unit`). -/
theorem FA_XcSout_Req : PrunableOneMsg "ClientInt" "Request" "unit" XcSout :=
  prunable_one_msg_extC_owner "ClientInt" _ "Request" "unit"
/-- One-message prunability of `XcSout` for (`ClientInt`, `Response`, `unit`). -/
theorem FA_XcSout_Resp : PrunableOneMsg "ClientInt" "Response" "unit" XcSout :=
  prunable_one_msg_extC_owner "ClientInt" _ "Response" "unit"
/-- One-message prunability of `XcSout` for (`ClientInt`, `Terminate`, `unit`). -/
theorem FA_XcSout_Term : PrunableOneMsg "ClientInt" "Terminate" "unit" XcSout :=
  prunable_one_msg_extC_owner "ClientInt" _ "Terminate" "unit"
/-- One-message prunability of `XcT` for (`ClientInt`, `Request`, `unit`). -/
theorem FA_XcT_Req : PrunableOneMsg "ClientInt" "Request" "unit" XcT :=
  prunable_one_msg_trec_of_succ "ClientInt" "Request" "unit" FA_XcSout_Req
/-- One-message prunability of `XcT` for (`ClientInt`, `Response`, `unit`). -/
theorem FA_XcT_Resp : PrunableOneMsg "ClientInt" "Response" "unit" XcT :=
  prunable_one_msg_trec_of_succ "ClientInt" "Response" "unit" FA_XcSout_Resp
/-- One-message prunability of `XcT` for (`ClientInt`, `Terminate`, `unit`). -/
theorem FA_XcT_Term : PrunableOneMsg "ClientInt" "Terminate" "unit" XcT :=
  prunable_one_msg_trec_of_succ "ClientInt" "Terminate" "unit" FA_XcSout_Term
/-- One-message prunability of `XcI1c` for (`ClientInt`, `Request`, `unit`). -/
theorem FA_XcI1c_Req : PrunableOneMsg "ClientInt" "Request" "unit" XcI1c := by
  apply prunable_one_msg_intC_of_step _ "ClientInt" "Request" "unit"
  intro V hS
  cases hS with
  | @intC _ x hmem hHas =>
    obtain ⟨r, l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
    exact FA_XcT_Req
/-- One-message prunability of `XcI1c` for (`ClientInt`, `Response`, `unit`). -/
theorem FA_XcI1c_Resp : PrunableOneMsg "ClientInt" "Response" "unit" XcI1c := by
  apply prunable_one_msg_intC_of_step _ "ClientInt" "Response" "unit"
  intro V hS
  cases hS with
  | @intC _ x hmem hHas =>
    obtain ⟨r, l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
    rw [Xc_has_Resp_XcT_false] at hHas
    cases hHas
/-- One-message prunability of `XcI1c` for (`ClientInt`, `Terminate`, `unit`). -/
theorem FA_XcI1c_Term : PrunableOneMsg "ClientInt" "Terminate" "unit" XcI1c := by
  apply prunable_one_msg_intC_of_step _ "ClientInt" "Terminate" "unit"
  intro V hS
  cases hS with
  | @intC _ x hmem hHas =>
    obtain ⟨r, l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
    exact FA_XcT_Term
/-- One-message prunability of `XcE3c` for (`ClientInt`, `Response`, `unit`). -/
theorem FA_XcE3c_Resp : PrunableOneMsg "ClientInt" "Response" "unit" XcE3c :=
  prunable_one_msg_extC_owner "ClientInt" _ "Response" "unit"
/-- One-message prunability of `XcSin` for (`ClientInt`, `Request`, `unit`). -/
theorem FA_XcSin_Req : PrunableOneMsg "ClientInt" "Request" "unit" XcSin := by
  apply prunable_one_msg_intC_of_step _ "ClientInt" "Request" "unit"
  intro V hS
  cases hS with
  | @intC _ x hmem hHas =>
    obtain ⟨r, l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · rw [Xc_has_Req_XcE3c_false] at hHas
      cases hHas
    · rw [Xc_has_End_Req_false] at hHas
      cases hHas
/-- One-message prunability of `XcSin` for (`ClientInt`, `Terminate`, `unit`). -/
theorem FA_XcSin_Term : PrunableOneMsg "ClientInt" "Terminate" "unit" XcSin := by
  apply prunable_one_msg_intC_of_step _ "ClientInt" "Terminate" "unit"
  intro V hS
  cases hS with
  | @intC _ x hmem hHas =>
    obtain ⟨r, l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · rw [Xc_has_Term_XcE3c_false] at hHas
      cases hHas
    · rw [Xc_has_End_Term_false] at hHas
      cases hHas
/-- One-message prunability of `XcI` for (`ClientInt`, `Request`, `unit`). -/
theorem FA_XcI_Req : PrunableOneMsg "ClientInt" "Request" "unit" XcI :=
  prunable_one_msg_trec_of_succ "ClientInt" "Request" "unit" FA_XcSin_Req
/-- One-message prunability of `XcI` for (`ClientInt`, `Terminate`, `unit`). -/
theorem FA_XcI_Term : PrunableOneMsg "ClientInt" "Terminate" "unit" XcI :=
  prunable_one_msg_trec_of_succ "ClientInt" "Terminate" "unit" FA_XcSin_Term

/-- One-message prunability of `XcSin` for (`ClientInt`, `Response`, `unit`). -/
theorem FA_XcSin_Resp : PrunableOneMsg "ClientInt" "Response" "unit" XcSin := by
  apply prunable_one_msg_intC_of_step _ "ClientInt" "Response" "unit"
  intro V hS
  cases hS with
  | @intC _ x hmem hHas =>
    obtain ⟨r, l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · exact FA_XcE3c_Resp
    · rw [Xc_has_End_Resp_false] at hHas
      cases hHas
/-- One-message prunability of `XcI` for (`ClientInt`, `Response`, `unit`). -/
theorem FA_XcI_Resp : PrunableOneMsg "ClientInt" "Response" "unit" XcI :=
  prunable_one_msg_trec_of_succ "ClientInt" "Response" "unit" FA_XcSin_Resp

/-- One-message prunability fact. -/
theorem hfaT_xc : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
    ExposedFrom XcT pm lab0 S0 → PrunableOneMsg pm lab0 S0 XcT := by
  intro pm lab0 S0 hexp
  cases hexp with
  | trec hsub =>
    cases hsub with
    | extC_here hmem =>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
      rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · exact FA_XcT_Req
      · exact FA_XcT_Term
    | extC_step hne hmem hsub2 =>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
      rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · cases hsub2 with
        | intC_step hmem2 hne2 hsub3 =>
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
          obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem2
          cases hsub3
      · cases hsub2 with
        | trec hsub3 =>
          cases hsub3 with
          | intC_step hmem3 hne3 hsub4 =>
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem3
            rcases hmem3 with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
            · cases hsub4 with
              | extC_here hmem5 =>
                simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem5
                obtain ⟨rfl, rfl, rfl⟩ := hmem5
                exact FA_XcT_Resp
              | extC_step hne5 hmem5 hsub6 =>
                simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem5
                obtain ⟨rfl, rfl, rfl⟩ := hmem5
                cases hsub6
            · cases hsub4

/-- One-message prunability fact. -/
theorem hfaI_xc : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
    ExposedFrom XcI pm lab0 S0 → PrunableOneMsg pm lab0 S0 XcI := by
  intro pm lab0 S0 hexp
  cases hexp with
  | trec hsub =>
    cases hsub with
    | intC_step hmem hne hsub2 =>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
      rcases hmem with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
      · cases hsub2 with
        | extC_here hmem2 =>
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
          obtain ⟨rfl, rfl, rfl⟩ := hmem2
          exact FA_XcI_Resp
        | extC_step hne2 hmem2 hsub3 =>
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
          obtain ⟨rfl, rfl, rfl⟩ := hmem2
          cases hsub3
      · cases hsub2

/-- One-message prunability fact. -/
theorem hfaE1c_xc : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
    ExposedFrom XcI1c pm lab0 S0 → PrunableOneMsg pm lab0 S0 XcI1c := by
  intro pm lab0 S0 hexp
  cases hexp with
  | intC_step hmem hne hsub =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
    apply prunable_one_msg_intC_of_step _ pm lab0 S0
    intro V hS
    cases hS with
    | @intC _ x hmem2 hHas2 =>
      obtain ⟨r, l, s, U⟩ := x
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem2
      exact hfaT_xc _ _ _ (has_to_exposed _ _ _ _ hHas2)

/-- One-message prunability fact. -/
theorem hfaE3c_xc : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
    ExposedFrom XcE3c pm lab0 S0 → PrunableOneMsg pm lab0 S0 XcE3c := by
  intro pm lab0 S0 hexp
  cases hexp with
  | extC_here hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    exact FA_XcE3c_Resp
  | extC_step hne hmem hsub =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    apply prunable_one_msg_extC_of_step "ClientInt" _ pm lab0 S0
    intro V hS
    cases hS with
    | @extCQ _ _ x _ hmem' _ =>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem'
      obtain ⟨rfl, rfl, rfl⟩ := hmem'
      exact hfaI_xc _ _ _ hsub

/-- One-message prunability fact. -/
theorem hfaSin_xc : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
    ExposedFrom XcSin pm lab0 S0 → PrunableOneMsg pm lab0 S0 XcSin := by
  intro pm lab0 S0 _
  apply prunable_one_msg_intC_of_step _ pm lab0 S0
  intro V hS
  cases hS with
  | @intC _ x hmem hHas =>
    obtain ⟨r, l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · exact hfaE3c_xc _ _ _ (has_to_exposed _ _ _ _ hHas)
    · exact prunable_one_msg_end _ _ _

/-- One-message prunability fact. -/
theorem hfaSout_xc : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
    ExposedFrom XcSout pm lab0 S0 → PrunableOneMsg pm lab0 S0 XcSout := by
  intro pm lab0 S0 hexp
  cases hexp with
  | extC_here hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact FA_XcSout_Req
    · exact FA_XcSout_Term
  | extC_step hne hmem hsub2 =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · apply prunable_one_msg_extC_of_step "ClientInt" _ pm lab0 S0
      intro V hS
      cases hS with
      | @extCQ _ _ x _ hmem2 hHas2 =>
        obtain ⟨l, s, U⟩ := x
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
        rcases hmem2 with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
        · exact hfaE1c_xc _ _ _ (has_to_exposed _ _ _ _ hHas2)
        · exact hfaI_xc _ _ _ (has_to_exposed _ _ _ _ hHas2)
    · apply prunable_one_msg_extC_of_step "ClientInt" _ pm lab0 S0
      intro V hS
      cases hS with
      | @extCQ _ _ x _ hmem2 hHas2 =>
        obtain ⟨l, s, U⟩ := x
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
        rcases hmem2 with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
        · exact hfaE1c_xc _ _ _ (has_to_exposed _ _ _ _ hHas2)
        · exact hfaI_xc _ _ _ (has_to_exposed _ _ _ _ hHas2)

/-- Deep adequacy of `XcT` with empty seen set. -/
theorem XcT_deep : Prunable [] XcT := by
  apply Prunable.trec_new [] "Outgoing" XcBout _ _ hfaT_xc
  · simp
  · rw [XcSout_subst]
    apply Prunable.extC [XcT] "ClientInt" _ _ hfaSout_xc
    intro x hmem
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with rfl | rfl
    · apply Prunable.intC [XcT] _ _ hfaE1c_xc
      intro y hmemY
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmemY
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hmemY
      exact Prunable.trec_seen [XcT] "Outgoing" XcBout
        (List.mem_cons.mpr (Or.inl rfl)) hfaT_xc
    · have hPrunableI : Prunable [XcT] XcI := by
        apply Prunable.trec_new [XcT] "Incoming" XcBin _ _ hfaI_xc
        · exact XcI_fresh
        · rw [XcSin_subst]
          apply Prunable.intC [XcI, XcT] _ _ hfaSin_xc
          intro z hmemZ
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmemZ
          rcases hmemZ with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
          · apply Prunable.extC [XcI, XcT] "ClientInt" _ _ hfaE3c_xc
            intro w hmemW
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmemW
            obtain ⟨rfl, rfl, rfl⟩ := hmemW
            exact Prunable.trec_seen [XcI, XcT] "Incoming" XcBin
              (List.mem_cons.mpr (Or.inl rfl)) hfaI_xc
          · exact Prunable.tEnd [XcI, XcT]
      exact hPrunableI


/-- Definitional unfolding: `XcT` is definitionally the stated type. -/
theorem XcT_eq : XcT = ClientExt := rfl

/-- Deep adequacy of `ClientExt` with empty seen set. -/
theorem ClientExt_deep : Prunable [] ClientExt := by
  rw [← XcT_eq]
  exact XcT_deep

/-- Monitorability of `ClientExt` (finite prune closure). -/
theorem ClientExt_mon : Drainability.Monitorable ClientExt := by
  have hRW : ClientExt = XcT := rfl
  rw [hRW]
  apply Monitorable_of_closed_set XcT
    {XcT, XcSout, XcI1c, XcI, XcSin, XcE3c, SessionType.tEnd,
     SessionType.tVar "Outgoing", SessionType.tVar "Incoming"}
  · simp
  · intro U hU V hStep
    simp only [Finset.mem_insert, Finset.mem_singleton] at hU
    rcases hU with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · cases hStep with
      | trec => rw [XcSout_subst]; simp
    · cases hStep with
      | extC hmem =>
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
        rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
        · simp
        · simp
    · cases hStep with
      | intC hmem =>
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
        simp
    · cases hStep with
      | trec => rw [XcSin_subst]; simp
    · cases hStep with
      | intC hmem =>
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
        rcases hmem with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · simp
        · simp
    · cases hStep with
      | extC hmem =>
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
        obtain ⟨rfl, rfl, rfl⟩ := hmem
        simp
    · cases hStep
    · cases hStep
    · cases hStep

/-- Empty-queue network for the two firewall roles. -/
def Net : Network :=
  [("ClientInt", (ClientInt, [])),
   ("ClientExt", (ClientExt, []))]

/-- `Net` is well-formed: distinct roles, well-formed types, vacuous sender-closure. -/
theorem Net_wellFormed : Net.WellFormed := by
  refine ⟨by decide, ?_, Network.SenderClosed_of_all_nil (by decide)⟩
  intro x hx
  simp only [Net, List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl
  · exact ClientInt.wfCheck_sound (by decide)
  · exact ClientExt.wfCheck_sound (by decide)

/-- `Net` has no self-mention: each role is absent from its own type. -/
theorem Net_noSelf : Net.NoSelf := by
  apply Network.NoSelf_of_rolesOf
  intro x hx
  simp only [Net, List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl <;> decide

/-- `Net` contains every role occurring in its member types. -/
theorem Net_rolesPresent : Net.RolesPresent := by
  intro q T Q s hmem hOcc
  have hmemR : s ∈ rolesOf T := occurs_mem hOcc
  simp only [Net, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · simp only [ClientInt, rolesOf, rolesOf.goInt, rolesOf.goExt,
      List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmemR
    rcases hmemR with (rfl | rfl) | rfl | rfl | rfl
    · exact ⟨(ClientExt, []), by decide⟩
    · exact ⟨(ClientExt, []), by decide⟩
    · exact ⟨(ClientExt, []), by decide⟩
    · exact ⟨(ClientExt, []), by decide⟩
    · exact ⟨(ClientExt, []), by decide⟩
  · simp only [ClientExt, rolesOf, rolesOf.goInt, rolesOf.goExt,
      List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmemR
    rcases hmemR with rfl | rfl | (rfl | rfl) | rfl
    · exact ⟨(ClientInt, []), by decide⟩
    · exact ⟨(ClientInt, []), by decide⟩
    · exact ⟨(ClientInt, []), by decide⟩
    · exact ⟨(ClientInt, []), by decide⟩
    · exact ⟨(ClientInt, []), by decide⟩

/-- `Net` admits a consistent coinductive instrumentation (empty queues fold trivially). -/
theorem Net_consistent : ∃ MN, consistentInstrumentation_co Net = some MN :=
  exists_consistentInstrumentation_co_of_all_nil Net (by decide)


-- ============ OUT-step characterizations ============
theorem FwT_out_iff {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans ClientInt (st_label.out "ClientExt" lab S) T' →
    (lab = "Request" ∧ S = "unit" ∧ T' = FwT1c) ∨
    (lab = "Terminate" ∧ S = "unit" ∧ T' = FwI) := by
  intro h
  unfold ClientInt at h
  cases h with
  | tRec hsub =>
    have h2 : st_trans FwSout (st_label.out "ClientExt" lab S) T' := hsub
    unfold FwSout at h2
    cases h2 with
    | intC hmem =>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
      rcases hmem with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl, rfl⟩

theorem XcT_no_out {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans ClientExt (st_label.out p lab S) T') : False := by
  unfold ClientExt at h
  cases h with
  | tRec hsub =>
    have h2 : st_trans XcSout (st_label.out p lab S) T' := hsub
    unfold XcSout at h2
    cases h2

theorem XcI1c_out_iff {p lab : Role} {S : DataSort} {T' : SessionType} :
    st_trans XcI1c (st_label.out p lab S) T' →
    p = "ClientInt" ∧ lab = "Response" ∧ S = "unit" ∧ T' = XcT := by
  intro h
  unfold XcI1c at h
  cases h with
  | intC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem FwT3c_out_iff {p lab : Role} {S : DataSort} {T' : SessionType} :
    st_trans FwT3c (st_label.out p lab S) T' →
    p = "ClientExt" ∧ lab = "Response" ∧ S = "unit" ∧ T' = FwI := by
  intro h
  unfold FwT3c at h
  cases h with
  | intC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem XcI_out_iff {p lab : Role} {S : DataSort} {T' : SessionType} :
    st_trans XcI (st_label.out p lab S) T' →
    (p = "ClientInt" ∧ lab = "Request" ∧ S = "unit" ∧ T' = XcE3c) ∨
    (p = "ClientInt" ∧ lab = "Terminate" ∧ S = "unit" ∧ T' = SessionType.tEnd) := by
  intro h
  unfold XcI at h
  cases h with
  | tRec hsub =>
    have h2 : st_trans XcSin (st_label.out p lab S) T' := hsub
    unfold XcSin at h2
    cases h2 with
    | intC hmem =>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
      rcases hmem with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl, rfl, rfl⟩

theorem FwT1c_no_out {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans FwT1c (st_label.out p lab S) T') : False := by
  unfold FwT1c at h
  cases h

theorem FwI_no_out {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans FwI (st_label.out p lab S) T') : False := by
  unfold FwI at h
  cases h with
  | tRec hsub =>
    have h2 : st_trans FwSin (st_label.out p lab S) T' := hsub
    unfold FwSin at h2
    cases h2

theorem XcE3c_no_out {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans XcE3c (st_label.out p lab S) T') : False := by
  unfold XcE3c at h
  cases h

theorem tEnd_no_out {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans SessionType.tEnd (st_label.out p lab S) T') : False := by
  cases h

-- ============ INP-step characterizations ============
theorem FwT_no_inp {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans ClientInt (st_label.inp p lab S) T') : False := by
  unfold ClientInt at h
  cases h with
  | tRec hsub =>
    have h2 : st_trans FwSout (st_label.inp p lab S) T' := hsub
    unfold FwSout at h2
    cases h2

theorem FwT1c_inp_iff {p lab : Role} {S : DataSort} {T' : SessionType} :
    st_trans FwT1c (st_label.inp p lab S) T' →
    p = "ClientExt" ∧ lab = "Response" ∧ S = "unit" ∧ T' = FwT := by
  intro h
  unfold FwT1c at h
  cases h with
  | extC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem FwI_inp_iff {p lab : Role} {S : DataSort} {T' : SessionType} :
    st_trans FwI (st_label.inp p lab S) T' →
    (p = "ClientExt" ∧ lab = "Request" ∧ S = "unit" ∧ T' = FwT3c) ∨
    (p = "ClientExt" ∧ lab = "Terminate" ∧ S = "unit" ∧ T' = SessionType.tEnd) := by
  intro h
  unfold FwI at h
  cases h with
  | tRec hsub =>
    have h2 : st_trans FwSin (st_label.inp p lab S) T' := hsub
    unfold FwSin at h2
    cases h2 with
    | extC hmem =>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
      rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl, rfl, rfl⟩

theorem FwT3c_no_inp {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans FwT3c (st_label.inp p lab S) T') : False := by
  unfold FwT3c at h
  cases h

theorem XcT_inp_iff {p lab : Role} {S : DataSort} {T' : SessionType} :
    st_trans ClientExt (st_label.inp p lab S) T' →
    (p = "ClientInt" ∧ lab = "Request" ∧ S = "unit" ∧ T' = XcI1c) ∨
    (p = "ClientInt" ∧ lab = "Terminate" ∧ S = "unit" ∧ T' = XcI) := by
  intro h
  unfold ClientExt at h
  cases h with
  | tRec hsub =>
    have h2 : st_trans XcSout (st_label.inp p lab S) T' := hsub
    unfold XcSout at h2
    cases h2 with
    | extC hmem =>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
      rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl, rfl, rfl⟩

theorem XcI1c_no_inp {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans XcI1c (st_label.inp p lab S) T') : False := by
  unfold XcI1c at h
  cases h

theorem XcE3c_inp_iff {p lab : Role} {S : DataSort} {T' : SessionType} :
    st_trans XcE3c (st_label.inp p lab S) T' →
    p = "ClientInt" ∧ lab = "Response" ∧ S = "unit" ∧ T' = XcI := by
  intro h
  unfold XcE3c at h
  cases h with
  | extC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem XcI_no_inp {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans XcI (st_label.inp p lab S) T') : False := by
  unfold XcI at h
  cases h with
  | tRec hsub =>
    have h2 : st_trans XcSin (st_label.inp p lab S) T' := hsub
    unfold XcSin at h2
    cases h2

theorem tEnd_no_inp {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans SessionType.tEnd (st_label.inp p lab S) T') : False := by
  cases h

-- ============ Reachable states (whole-network enumeration) ============
-- Messages
abbrev mReqIE : QueueMessage := QueueMessage.msg "ClientInt" "Request" "unit"
abbrev mTermIE : QueueMessage := QueueMessage.msg "ClientInt" "Terminate" "unit"
abbrev mRespEI : QueueMessage := QueueMessage.msg "ClientExt" "Response" "unit"
abbrev mReqEI : QueueMessage := QueueMessage.msg "ClientExt" "Request" "unit"
abbrev mTermEI : QueueMessage := QueueMessage.msg "ClientExt" "Terminate" "unit"
abbrev mRespIE : QueueMessage := QueueMessage.msg "ClientInt" "Response" "unit"

def S0 : Network := [("ClientInt", (ClientInt, [])), ("ClientExt", (ClientExt, []))]
def S1 : Network := [("ClientExt", (ClientExt, [mReqIE])), ("ClientInt", (FwT1c, []))]
def S2 : Network := [("ClientExt", (XcI1c, [])), ("ClientInt", (FwT1c, []))]
def S3 : Network := [("ClientInt", (FwT1c, [mRespEI])), ("ClientExt", (ClientExt, []))]
def S5 : Network := [("ClientExt", (ClientExt, [mTermIE])), ("ClientInt", (FwI, []))]
def S6 : Network := [("ClientExt", (XcI, [])), ("ClientInt", (FwI, []))]
def S7 : Network := [("ClientInt", (FwI, [mReqEI])), ("ClientExt", (XcE3c, []))]
def S8 : Network := [("ClientInt", (FwT3c, [])), ("ClientExt", (XcE3c, []))]
def S9 : Network := [("ClientExt", (XcE3c, [mRespIE])), ("ClientInt", (FwI, []))]
def S11 : Network := [("ClientInt", (FwI, [mTermEI])), ("ClientExt", (SessionType.tEnd, []))]
def S12 : Network := [("ClientInt", (SessionType.tEnd, [])), ("ClientExt", (SessionType.tEnd, []))]

-- Queue computations
theorem qReqIE_req : Queue.dequeue [mReqIE] mReqIE = some ([] : Queue) := rfl
theorem qReqIE_term : Queue.dequeue [mReqIE] (QueueMessage.msg "ClientInt" "Terminate" "unit") = none := rfl
theorem qRespEI_resp : Queue.dequeue [mRespEI] mRespEI = some ([] : Queue) := rfl
theorem qTermIE_req : Queue.dequeue [mTermIE] (QueueMessage.msg "ClientInt" "Request" "unit") = none := rfl
theorem qTermIE_term : Queue.dequeue [mTermIE] mTermIE = some ([] : Queue) := rfl
theorem qReqEI_req : Queue.dequeue [mReqEI] mReqEI = some ([] : Queue) := rfl
theorem qReqEI_term : Queue.dequeue [mReqEI] (QueueMessage.msg "ClientExt" "Terminate" "unit") = none := rfl
theorem qRespIE_resp : Queue.dequeue [mRespIE] mRespIE = some ([] : Queue) := rfl
theorem qTermEI_req : Queue.dequeue [mTermEI] (QueueMessage.msg "ClientExt" "Request" "unit") = none := rfl
theorem qTermEI_term : Queue.dequeue [mTermEI] mTermEI = some ([] : Queue) := rfl

theorem S0_step : ∀ (δ : net_label) (N' : Network),
    net_trans S0 δ N' → is_internal_net_label δ → N' = S1 ∨ N' = S5 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S0, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S0, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := FwT_out_iff hST
          rcases ho with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
          · exact Or.inl rfl
          · exact Or.inr rfl
    · cases h_send with
      | send hST => exact absurd hST (fun h => XcT_no_out h)
    · exact absurd rfl hne

theorem S1_step : ∀ (δ : net_label) (N' : Network),
    net_trans S1 δ N' → is_internal_net_label δ → N' = S2 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S1, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := XcT_inp_iff hST
        rcases hi with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · rw [qReqIE_req] at hQ
          cases hQ
          rfl
        · rw [qReqIE_term] at hQ
          cases hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S1, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => XcT_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => FwT1c_no_out h)
    · exact absurd rfl hne

theorem S2_step : ∀ (δ : net_label) (N' : Network),
    net_trans S2 δ N' → is_internal_net_label δ → N' = S3 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S2, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S2, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := XcI1c_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          rfl
    · cases h_send with
      | send hST => exact absurd hST (fun h => FwT1c_no_out h)
    · exact absurd rfl hne

theorem S5_step : ∀ (δ : net_label) (N' : Network),
    net_trans S5 δ N' → is_internal_net_label δ → N' = S6 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S5, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := XcT_inp_iff hST
        rcases hi with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · rw [qTermIE_req] at hQ
          cases hQ
        · rw [qTermIE_term] at hQ
          cases hQ
          rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S5, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => XcT_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => FwI_no_out h)
    · exact absurd rfl hne

theorem S6_step : ∀ (δ : net_label) (N' : Network),
    net_trans S6 δ N' → is_internal_net_label δ → N' = S7 ∨ N' = S11 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S6, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S6, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := XcI_out_iff hST
          rcases ho with ⟨-, rfl, rfl, rfl⟩ | ⟨-, rfl, rfl, rfl⟩
          · exact Or.inl rfl
          · exact Or.inr rfl
    · cases h_send with
      | send hST => exact absurd hST (fun h => FwI_no_out h)
    · exact absurd rfl hne

theorem S7_step : ∀ (δ : net_label) (N' : Network),
    net_trans S7 δ N' → is_internal_net_label δ → N' = S8 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S7, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := FwI_inp_iff hST
        rcases hi with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · rw [qReqEI_req] at hQ
          cases hQ
          rfl
        · rw [qReqEI_term] at hQ
          cases hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S7, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => FwI_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => XcE3c_no_out h)
    · exact absurd rfl hne
theorem S3_step : ∀ (δ : net_label) (N' : Network),
    net_trans S3 δ N' → is_internal_net_label δ → N' = S0 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S3, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := FwT1c_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qRespEI_resp] at hQ
        cases hQ
        rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S3, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => FwT1c_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => XcT_no_out h)
    · exact absurd rfl hne

theorem S8_step : ∀ (δ : net_label) (N' : Network),
    net_trans S8 δ N' → is_internal_net_label δ → N' = S9 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S8, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S8, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := FwT3c_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          rfl
    · cases h_send with
      | send hST => exact absurd hST (fun h => XcE3c_no_out h)
    · exact absurd rfl hne

theorem S9_step : ∀ (δ : net_label) (N' : Network),
    net_trans S9 δ N' → is_internal_net_label δ → N' = S6 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S9, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := XcE3c_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qRespIE_resp] at hQ
        cases hQ
        rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S9, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => XcE3c_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => FwI_no_out h)
    · exact absurd rfl hne

theorem S11_step : ∀ (δ : net_label) (N' : Network),
    net_trans S11 δ N' → is_internal_net_label δ → N' = S12 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S11, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := FwI_inp_iff hST
        rcases hi with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · rw [qTermEI_req] at hQ
          cases hQ
        · rw [qTermEI_term] at hQ
          cases hQ
          rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S11, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => FwI_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · exact absurd rfl hne

theorem S12_no_step : ∀ (δ : net_label) (N' : Network),
    net_trans S12 δ N' → is_internal_net_label δ → False := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S12, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      (cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ)
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S12, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · exact absurd rfl hne

-- Reachability: every τ-reachable network is one of the 11 states.
-- (Auxiliary with variable start so `induction` applies; instantiate at `Net`.)
theorem fwReach_aux : ∀ (N1 N2 : Network), net_trans_star N1 N2 →
    (N1 = S0 ∨ N1 = S1 ∨ N1 = S2 ∨ N1 = S3 ∨ N1 = S5 ∨ N1 = S6 ∨
    N1 = S7 ∨ N1 = S8 ∨ N1 = S9 ∨ N1 = S11 ∨ N1 = S12) →
    (N2 = S0 ∨ N2 = S1 ∨ N2 = S2 ∨ N2 = S3 ∨ N2 = S5 ∨ N2 = S6 ∨
    N2 = S7 ∨ N2 = S8 ∨ N2 = S9 ∨ N2 = S11 ∨ N2 = S12) := by
  intro N1 N2 hStar
  induction hStar with
  | refl => intro h; exact h
  | step hInt hTr _ ih =>
    intro hN1
    rcases hN1 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h := S0_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S1_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S2_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S3_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S5_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S6_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S7_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S8_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S9_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S11_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · exact absurd (S12_no_step _ _ hTr hInt) id

theorem fwReach : ∀ (N' : Network), net_trans_star Net N' →
    (N' = S0 ∨ N' = S1 ∨ N' = S2 ∨ N' = S3 ∨ N' = S5 ∨ N' = S6 ∨
    N' = S7 ∨ N' = S8 ∨ N' = S9 ∨ N' = S11 ∨ N' = S12) :=
  fun N' hStar => fwReach_aux Net N' hStar (Or.inl rfl)

-- ============ Explicit transitions (reused for stuck + output-live) ============
theorem t01 : net_trans S0 (net_label.τ_comm "ClientInt" "ClientExt" "Request" "unit") S1 := by
  have h_send : sq_trans (ClientInt, ([] : Queue))
      (sq_action.send "ClientExt" "Request" "unit") (FwT1c, []) := by
    apply sq_trans.send
    unfold ClientInt
    apply st_trans.tRec
    show st_trans FwSout _ _
    unfold FwSout
    apply st_trans.intC
    simp [FwT1c]
  have h_recv : sq_trans (ClientExt, ([] : Queue))
      (sq_action.recv "ClientInt" "Request" "unit") (ClientExt, [mReqIE]) :=
    sq_trans.recv
  have hmem_p : ("ClientInt", (ClientInt, ([] : Queue))) ∈ S0 := by simp [S0]
  have hmem_q : ("ClientExt", (ClientExt, ([] : Queue))) ∈ S0 := by simp [S0]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t05 : net_trans S0 (net_label.τ_comm "ClientInt" "ClientExt" "Terminate" "unit") S5 := by
  have h_send : sq_trans (ClientInt, ([] : Queue))
      (sq_action.send "ClientExt" "Terminate" "unit") (FwI, []) := by
    apply sq_trans.send
    unfold ClientInt
    apply st_trans.tRec
    show st_trans FwSout _ _
    unfold FwSout
    apply st_trans.intC
    simp [FwI]
  have h_recv : sq_trans (ClientExt, ([] : Queue))
      (sq_action.recv "ClientInt" "Terminate" "unit") (ClientExt, [mTermIE]) :=
    sq_trans.recv
  have hmem_p : ("ClientInt", (ClientInt, ([] : Queue))) ∈ S0 := by simp [S0]
  have hmem_q : ("ClientExt", (ClientExt, ([] : Queue))) ∈ S0 := by simp [S0]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t12 : net_trans S1 (net_label.τ_dequeue "ClientExt" "ClientInt" "Request" "unit") S2 := by
  have hSQ : sq_trans (ClientExt, [mReqIE])
      (sq_action.dequeue "ClientInt" "Request" "unit") (XcI1c, []) := by
    apply sq_trans.dequeue
    · unfold ClientExt
      apply st_trans.tRec
      show st_trans XcSout _ _
      unfold XcSout
      apply st_trans.extC
      simp [XcI1c]
    · exact qReqIE_req
  have hmem : ("ClientExt", (ClientExt, [mReqIE])) ∈ S1 := by simp [S1]
  exact net_trans.dequeue hSQ hmem

theorem t23 : net_trans S2 (net_label.τ_comm "ClientExt" "ClientInt" "Response" "unit") S3 := by
  have h_send : sq_trans (XcI1c, ([] : Queue))
      (sq_action.send "ClientInt" "Response" "unit") (XcT, []) := by
    apply sq_trans.send
    unfold XcI1c
    apply st_trans.intC
    simp [XcT]
  have h_recv : sq_trans (FwT1c, ([] : Queue))
      (sq_action.recv "ClientExt" "Response" "unit") (FwT1c, [mRespEI]) :=
    sq_trans.recv
  have hmem_p : ("ClientExt", (XcI1c, ([] : Queue))) ∈ S2 := by simp [S2]
  have hmem_q : ("ClientInt", (FwT1c, ([] : Queue))) ∈ S2 := by simp [S2]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t30 : net_trans S3 (net_label.τ_dequeue "ClientInt" "ClientExt" "Response" "unit") S0 := by
  have hSQ : sq_trans (FwT1c, [mRespEI])
      (sq_action.dequeue "ClientExt" "Response" "unit") (FwT, []) := by
    apply sq_trans.dequeue
    · unfold FwT1c
      apply st_trans.extC
      simp [FwT]
    · exact qRespEI_resp
  have hmem : ("ClientInt", (FwT1c, [mRespEI])) ∈ S3 := by simp [S3]
  exact net_trans.dequeue hSQ hmem

theorem t56 : net_trans S5 (net_label.τ_dequeue "ClientExt" "ClientInt" "Terminate" "unit") S6 := by
  have hSQ : sq_trans (ClientExt, [mTermIE])
      (sq_action.dequeue "ClientInt" "Terminate" "unit") (XcI, []) := by
    apply sq_trans.dequeue
    · unfold ClientExt
      apply st_trans.tRec
      show st_trans XcSout _ _
      unfold XcSout
      apply st_trans.extC
      simp [XcI]
    · exact qTermIE_term
  have hmem : ("ClientExt", (ClientExt, [mTermIE])) ∈ S5 := by simp [S5]
  exact net_trans.dequeue hSQ hmem

theorem t67 : net_trans S6 (net_label.τ_comm "ClientExt" "ClientInt" "Request" "unit") S7 := by
  have h_send : sq_trans (XcI, ([] : Queue))
      (sq_action.send "ClientInt" "Request" "unit") (XcE3c, []) := by
    apply sq_trans.send
    unfold XcI
    apply st_trans.tRec
    show st_trans XcSin _ _
    unfold XcSin
    apply st_trans.intC
    simp [XcE3c]
  have h_recv : sq_trans (FwI, ([] : Queue))
      (sq_action.recv "ClientExt" "Request" "unit") (FwI, [mReqEI]) :=
    sq_trans.recv
  have hmem_p : ("ClientExt", (XcI, ([] : Queue))) ∈ S6 := by simp [S6]
  have hmem_q : ("ClientInt", (FwI, ([] : Queue))) ∈ S6 := by simp [S6]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t611 : net_trans S6 (net_label.τ_comm "ClientExt" "ClientInt" "Terminate" "unit") S11 := by
  have h_send : sq_trans (XcI, ([] : Queue))
      (sq_action.send "ClientInt" "Terminate" "unit") (SessionType.tEnd, []) := by
    apply sq_trans.send
    unfold XcI
    apply st_trans.tRec
    show st_trans XcSin _ _
    unfold XcSin
    apply st_trans.intC
    simp
  have h_recv : sq_trans (FwI, ([] : Queue))
      (sq_action.recv "ClientExt" "Terminate" "unit") (FwI, [mTermEI]) :=
    sq_trans.recv
  have hmem_p : ("ClientExt", (XcI, ([] : Queue))) ∈ S6 := by simp [S6]
  have hmem_q : ("ClientInt", (FwI, ([] : Queue))) ∈ S6 := by simp [S6]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t78 : net_trans S7 (net_label.τ_dequeue "ClientInt" "ClientExt" "Request" "unit") S8 := by
  have hSQ : sq_trans (FwI, [mReqEI])
      (sq_action.dequeue "ClientExt" "Request" "unit") (FwT3c, []) := by
    apply sq_trans.dequeue
    · unfold FwI
      apply st_trans.tRec
      show st_trans FwSin _ _
      unfold FwSin
      apply st_trans.extC
      simp [FwT3c]
    · exact qReqEI_req
  have hmem : ("ClientInt", (FwI, [mReqEI])) ∈ S7 := by simp [S7]
  exact net_trans.dequeue hSQ hmem

theorem t89 : net_trans S8 (net_label.τ_comm "ClientInt" "ClientExt" "Response" "unit") S9 := by
  have h_send : sq_trans (FwT3c, ([] : Queue))
      (sq_action.send "ClientExt" "Response" "unit") (FwI, []) := by
    apply sq_trans.send
    unfold FwT3c
    apply st_trans.intC
    simp [FwI]
  have h_recv : sq_trans (XcE3c, ([] : Queue))
      (sq_action.recv "ClientInt" "Response" "unit") (XcE3c, [mRespIE]) :=
    sq_trans.recv
  have hmem_p : ("ClientInt", (FwT3c, ([] : Queue))) ∈ S8 := by simp [S8]
  have hmem_q : ("ClientExt", (XcE3c, ([] : Queue))) ∈ S8 := by simp [S8]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t96 : net_trans S9 (net_label.τ_dequeue "ClientExt" "ClientInt" "Response" "unit") S6 := by
  have hSQ : sq_trans (XcE3c, [mRespIE])
      (sq_action.dequeue "ClientInt" "Response" "unit") (XcI, []) := by
    apply sq_trans.dequeue
    · unfold XcE3c
      apply st_trans.extC
      simp [XcI]
    · exact qRespIE_resp
  have hmem : ("ClientExt", (XcE3c, [mRespIE])) ∈ S9 := by simp [S9]
  exact net_trans.dequeue hSQ hmem

theorem t1112 : net_trans S11 (net_label.τ_dequeue "ClientInt" "ClientExt" "Terminate" "unit") S12 := by
  have hSQ : sq_trans (FwI, [mTermEI])
      (sq_action.dequeue "ClientExt" "Terminate" "unit") (SessionType.tEnd, []) := by
    apply sq_trans.dequeue
    · unfold FwI
      apply st_trans.tRec
      show st_trans FwSin _ _
      unfold FwSin
      apply st_trans.extC
      simp
    · exact qTermEI_term
  have hmem : ("ClientInt", (FwI, [mTermEI])) ∈ S11 := by simp [S11]
  exact net_trans.dequeue hSQ hmem

-- ============ Half-duplex ============
/-- `Net` is half-duplex: opposite queues never both fill. -/
theorem Net_halfDuplex : IsHalfDuplex Net := by
  intro N' hStar p q Qp Qq hP hQ hCp hCq
  have hR := fwReach N' hStar
  rcases hR with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- S0: both queues empty
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S0, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      exact absurd hCp noContainsNil
  · -- S1: E has [Req from Int], I empty
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S1, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S2: both empty
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S2, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      exact absurd hCp noContainsNil
  · -- S3: I has [Resp from Ext], E empty
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S3, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S5: E has [Term from Int], I empty
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S5, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S6: both empty
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S6, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      exact absurd hCp noContainsNil
  · -- S7: I has [Req from Ext], E empty
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S7, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S8: both empty
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S8, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      exact absurd hCp noContainsNil
  · -- S9: E has [Resp from Int], I empty
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S9, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S11: I has [Term from Ext], E empty
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S11, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S12: both empty
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S12, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      exact absurd hCp noContainsNil

-- ============ Output-liveness: infinite fair paths ============
/-- Every infinite fair path from `Net` is output-live. -/
theorem fwOL_inf : IsOutputLiveInfinitePathNetwork Net := by
  intro path h0 hfair i p Qp hmemP q lab S hdeq
  have hStar : net_trans_star Net (path.seq i) := path_star_reachable h0 i
  have hR := fwReach _ hStar
  rcases hR with h | h | h | h | h | h | h | h | h | h | h
  · -- S0: queues empty, hdeq impossible
    rw [h] at hmemP
    obtain ⟨T, hP⟩ := hmemP
    simp only [S0, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      (obtain ⟨Q', hQ⟩ := hdeq; simp [Queue.dequeue, Queue.dequeue.go] at hQ)
  · -- S1: E holds [Req from Int]
    rw [h] at hmemP
    obtain ⟨T, hP⟩ := hmemP
    simp only [S1, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mReqIE] := Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      have hq : q = "ClientInt" := congrArg (fun m => m.1) hmem
      have hlab : lab = "Request" := congrArg (fun m => m.2) hmem
      have hS : S = "unit" := congrArg (fun m => m.3) hmem
      subst hq; subst hlab; subst hS
      exact (hfair i).2 "ClientExt" "ClientInt" "Request" "unit"
        ⟨S2, by rw [h]; exact t12⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- S2: queues empty
    rw [h] at hmemP
    obtain ⟨T, hP⟩ := hmemP
    simp only [S2, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      (obtain ⟨Q', hQ⟩ := hdeq; simp [Queue.dequeue, Queue.dequeue.go] at hQ)
  · -- S3: I holds [Resp from Ext]
    rw [h] at hmemP
    obtain ⟨T, hP⟩ := hmemP
    simp only [S3, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mRespEI] := Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      have hq : q = "ClientExt" := congrArg (fun m => m.1) hmem
      have hlab : lab = "Response" := congrArg (fun m => m.2) hmem
      have hS : S = "unit" := congrArg (fun m => m.3) hmem
      subst hq; subst hlab; subst hS
      exact (hfair i).2 "ClientInt" "ClientExt" "Response" "unit"
        ⟨S0, by rw [h]; exact t30⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- S5: E holds [Term from Int]
    rw [h] at hmemP
    obtain ⟨T, hP⟩ := hmemP
    simp only [S5, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mTermIE] := Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      have hq : q = "ClientInt" := congrArg (fun m => m.1) hmem
      have hlab : lab = "Terminate" := congrArg (fun m => m.2) hmem
      have hS : S = "unit" := congrArg (fun m => m.3) hmem
      subst hq; subst hlab; subst hS
      exact (hfair i).2 "ClientExt" "ClientInt" "Terminate" "unit"
        ⟨S6, by rw [h]; exact t56⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- S6: queues empty
    rw [h] at hmemP
    obtain ⟨T, hP⟩ := hmemP
    simp only [S6, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      (obtain ⟨Q', hQ⟩ := hdeq; simp [Queue.dequeue, Queue.dequeue.go] at hQ)
  · -- S7: I holds [Req from Ext]
    rw [h] at hmemP
    obtain ⟨T, hP⟩ := hmemP
    simp only [S7, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mReqEI] := Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      have hq : q = "ClientExt" := congrArg (fun m => m.1) hmem
      have hlab : lab = "Request" := congrArg (fun m => m.2) hmem
      have hS : S = "unit" := congrArg (fun m => m.3) hmem
      subst hq; subst hlab; subst hS
      exact (hfair i).2 "ClientInt" "ClientExt" "Request" "unit"
        ⟨S8, by rw [h]; exact t78⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- S8: queues empty
    rw [h] at hmemP
    obtain ⟨T, hP⟩ := hmemP
    simp only [S8, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      (obtain ⟨Q', hQ⟩ := hdeq; simp [Queue.dequeue, Queue.dequeue.go] at hQ)
  · -- S9: E holds [Resp from Int]
    rw [h] at hmemP
    obtain ⟨T, hP⟩ := hmemP
    simp only [S9, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mRespIE] := Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      have hq : q = "ClientInt" := congrArg (fun m => m.1) hmem
      have hlab : lab = "Response" := congrArg (fun m => m.2) hmem
      have hS : S = "unit" := congrArg (fun m => m.3) hmem
      subst hq; subst hlab; subst hS
      exact (hfair i).2 "ClientExt" "ClientInt" "Response" "unit"
        ⟨S6, by rw [h]; exact t96⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- S11: I holds [Term from Ext]
    rw [h] at hmemP
    obtain ⟨T, hP⟩ := hmemP
    simp only [S11, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mTermEI] := Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      have hq : q = "ClientExt" := congrArg (fun m => m.1) hmem
      have hlab : lab = "Terminate" := congrArg (fun m => m.2) hmem
      have hS : S = "unit" := congrArg (fun m => m.3) hmem
      subst hq; subst hlab; subst hS
      exact (hfair i).2 "ClientInt" "ClientExt" "Terminate" "unit"
        ⟨S12, by rw [h]; exact t1112⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- S12: queues empty
    rw [h] at hmemP
    obtain ⟨T, hP⟩ := hmemP
    simp only [S12, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      (obtain ⟨Q', hQ⟩ := hdeq; simp [Queue.dequeue, Queue.dequeue.go] at hQ)

-- ============ Output-liveness: stuck states have no orphans ============
/-- Every reachable stuck network from `Net` has no orphans. -/
theorem fwOL_stuck : ∀ (N' : Network), net_trans_star Net N' →
    IsStuckNetwork N' → NoOrphanMessages N' := by
  intro N' hStar hStuck
  have hR := fwReach N' hStar
  rcases hR with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exfalso
    exact hStuck ⟨_, _, by trivial, t01⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t12⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t23⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t30⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t56⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t67⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t78⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t89⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t96⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t1112⟩
  · intro r T Q p lab S Q' hmem hQ
    simp only [S12, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      simp [Queue.dequeue, Queue.dequeue.go] at hQ

/-- `Net` is output-live: fair paths drain queues, stuck states are clean. -/
theorem Net_outputLive : IsOutputLiveNetwork Net :=
  ⟨fwOL_inf, fwOL_stuck⟩

end Firewall

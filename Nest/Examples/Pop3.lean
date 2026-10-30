import Nest.SessionUtils
import Nest.SessionAdequacy
import Nest.Tests.PrunableTest
import Nest.Drainability
import Nest.Examples.ProofUtils
import Nest.MonitorLTSCo
import Nest.MonitorCoFun

namespace Pop3

/- Session types from the NEST P4 testbed:
   `NEST/nest/nest_scala/src/main/scala/examples/09_pop3.scala`
   (Scala package `pop3`; file `09_pop3.scala` maps to this module
   since Lean module names may not start with a digit).
   Translated below are the two `lst_*` local session types
   (`lst_POPClient`, `lst_POPServer`). Switch setup, IP rules, port
   checks and monitor wiring from `setup` are not session types and
   are not translated. Translation conventions: `IntChoice` branches
   become `internalChoice` branches `(agent, label, sort, cont)`;
   `ExtChoice` branches become `externalChoice` branches
   `(label, sort, cont)`; `Rec`/`Var`/`End` become `tRec`/`tVar`/`tEnd`.
   Agents become roles, labels stay labels. The Scala types carry no
   payload sorts, so every branch uses the placeholder sort `"unit"`. -/

/-- `lst_POPClient`. -/
def POPClient : SessionType :=
  SessionType.tRec "TryLogin"
    (SessionType.internalChoice
      [("POPServer", "USER", "unit",
        SessionType.externalChoice "POPServer"
          [("ERR", "unit",
            SessionType.tVar "TryLogin"),
          ("OK", "unit",
            SessionType.internalChoice
              [("POPServer", "PASS", "unit",
                SessionType.externalChoice "POPServer"
                  [("ERR", "unit",
                    SessionType.tVar "TryLogin"),
                  ("OK", "unit",
                    SessionType.tRec "ClientQuery"
                      (SessionType.internalChoice
                        [("POPServer", "LIST", "unit",
                          SessionType.externalChoice "POPServer"
                            [("MSGS", "unit",
                              SessionType.tVar "ClientQuery")]),
                        ("POPServer", "RETR", "unit",
                          SessionType.externalChoice "POPServer"
                            [("OK", "unit",
                              SessionType.tVar "ClientQuery"),
                            ("ERR", "unit",
                              SessionType.tVar "ClientQuery")]),
                        ("POPServer", "DELE", "unit",
                          SessionType.externalChoice "POPServer"
                            [("OK", "unit",
                              SessionType.tVar "ClientQuery"),
                            ("ERR", "unit",
                              SessionType.tVar "ClientQuery")]),
                        ("POPServer", "NOOP", "unit",
                          SessionType.externalChoice "POPServer"
                            [("OK", "unit",
                              SessionType.tVar "ClientQuery")]),
                        ("POPServer", "QUIT", "unit",
                          SessionType.externalChoice "POPServer"
                            [("OK", "unit",
                              SessionType.tEnd)])]))])])])])

/-- `lst_POPServer`. -/
def POPServer : SessionType :=
  SessionType.tRec "TryLogin"
    (SessionType.externalChoice "POPClient"
      [("USER", "unit",
        SessionType.internalChoice
          [("POPClient", "ERR", "unit",
            SessionType.tVar "TryLogin"),
          ("POPClient", "OK", "unit",
            SessionType.externalChoice "POPClient"
              [("PASS", "unit",
                SessionType.internalChoice
                  [("POPClient", "ERR", "unit",
                    SessionType.tVar "TryLogin"),
                  ("POPClient", "OK", "unit",
                    SessionType.tRec "ClientQuery"
                      (SessionType.externalChoice "POPClient"
                        [("LIST", "unit",
                          SessionType.internalChoice
                            [("POPClient", "MSGS", "unit",
                              SessionType.tVar "ClientQuery")]),
                        ("RETR", "unit",
                          SessionType.internalChoice
                            [("POPClient", "OK", "unit",
                              SessionType.tVar "ClientQuery"),
                            ("POPClient", "ERR", "unit",
                              SessionType.tVar "ClientQuery")]),
                        ("DELE", "unit",
                          SessionType.internalChoice
                            [("POPClient", "OK", "unit",
                              SessionType.tVar "ClientQuery"),
                            ("POPClient", "ERR", "unit",
                              SessionType.tVar "ClientQuery")]),
                        ("NOOP", "unit",
                          SessionType.internalChoice
                            [("POPClient", "OK", "unit",
                              SessionType.tVar "ClientQuery")]),
                        ("QUIT", "unit",
                          SessionType.internalChoice
                            [("POPClient", "OK", "unit",
                              SessionType.tEnd)])]))])])])])


-- Mirror defs for `POPClient`, outer loop (ungrafted; vars kept)
/-- External offer by `POPServer`: `(MSGS, unit)` looping on `ClientQuery` (`POPClient` mirror). -/
def PCList : SessionType :=
  SessionType.externalChoice "POPServer" [("MSGS", "unit", SessionType.tVar "ClientQuery")]
/-- External offer by `POPServer`: `(OK, unit)` looping on `ClientQuery`; `(ERR, unit)` looping
   on `ClientQuery` (`POPClient` mirror). -/
def PCRetr : SessionType :=
  SessionType.externalChoice "POPServer"
    [("OK", "unit", SessionType.tVar "ClientQuery"),
     ("ERR", "unit", SessionType.tVar "ClientQuery")]
/-- External offer by `POPServer`: `(OK, unit)` looping on `ClientQuery`; `(ERR, unit)` looping
   on `ClientQuery` (`POPClient` mirror). -/
def PCDele : SessionType :=
  SessionType.externalChoice "POPServer"
    [("OK", "unit", SessionType.tVar "ClientQuery"),
     ("ERR", "unit", SessionType.tVar "ClientQuery")]
/-- External offer by `POPServer`: `(OK, unit)` looping on `ClientQuery` (`POPClient` mirror). -/
def PCNoop : SessionType :=
  SessionType.externalChoice "POPServer"
    [("OK", "unit", SessionType.tVar "ClientQuery")]
/-- External offer by `POPServer`: `(OK, unit)` ending in `tEnd` (`POPClient` mirror). -/
def PCQuit : SessionType :=
  SessionType.externalChoice "POPServer"
    [("OK", "unit", SessionType.tEnd)]
/-- Internal choice: `(POPServer, LIST, unit)` continuing as `PCList`; `(POPServer, RETR, unit)`
   continuing as `PCRetr`; `(POPServer, DELE, unit)` continuing as `PCDele`; `(POPServer, NOOP,
   unit)` continuing as `PCNoop`; `(POPServer, QUIT, unit)` continuing as `PCQuit` (`POPClient`
   mirror). -/
def PCQBody : SessionType :=
  SessionType.internalChoice
    [("POPServer", "LIST", "unit", PCList),
     ("POPServer", "RETR", "unit", PCRetr),
     ("POPServer", "DELE", "unit", PCDele),
     ("POPServer", "NOOP", "unit", PCNoop),
     ("POPServer", "QUIT", "unit", PCQuit)]
/-- Recursive type: loop on `ClientQuery` with body `PCQBody` (`POPClient` mirror). -/
def PCQRec := SessionType.tRec "ClientQuery" PCQBody
/-- External offer by `POPServer`: `(ERR, unit)` looping on `TryLogin`; `(OK, unit)` continuing
   as `PCQRec` (`POPClient` mirror). -/
def PCPassE : SessionType :=
  SessionType.externalChoice "POPServer"
    [("ERR", "unit", SessionType.tVar "TryLogin"),
     ("OK", "unit", PCQRec)]
/-- Internal choice: `(POPServer, PASS, unit)` continuing as `PCPassE` (`POPClient` mirror). -/
def PCPass : SessionType :=
  SessionType.internalChoice [("POPServer", "PASS", "unit", PCPassE)]
/-- External offer by `POPServer`: `(ERR, unit)` looping on `TryLogin`; `(OK, unit)` continuing
   as `PCPass` (`POPClient` mirror). -/
def PCUser : SessionType :=
  SessionType.externalChoice "POPServer"
    [("ERR", "unit", SessionType.tVar "TryLogin"),
     ("OK", "unit", PCPass)]
/-- Internal choice: `(POPServer, USER, unit)` continuing as `PCUser` (`POPClient` mirror). -/
def PCBody : SessionType :=
  SessionType.internalChoice [("POPServer", "USER", "unit", PCUser)]
/-- Recursive type: loop on `TryLogin` with body `PCBody` (`POPClient` mirror). -/
def PCRec := SessionType.tRec "TryLogin" PCBody
-- Grafted outer (TryLogin-vars point at the outer rec)
/-- External offer by `POPServer`: `(MSGS, unit)` continuing as `PCQRec` (`POPClient` mirror). -/
def PCListS : SessionType :=
  SessionType.externalChoice "POPServer" [("MSGS", "unit", PCQRec)]
/-- External offer by `POPServer`: `(OK, unit)` continuing as `PCQRec`; `(ERR, unit)` continuing
   as `PCQRec` (`POPClient` mirror). -/
def PCRetrS : SessionType :=
  SessionType.externalChoice "POPServer"
    [("OK", "unit", PCQRec), ("ERR", "unit", PCQRec)]
/-- External offer by `POPServer`: `(OK, unit)` continuing as `PCQRec`; `(ERR, unit)` continuing
   as `PCQRec` (`POPClient` mirror). -/
def PCDeleS : SessionType :=
  SessionType.externalChoice "POPServer"
    [("OK", "unit", PCQRec), ("ERR", "unit", PCQRec)]
/-- External offer by `POPServer`: `(OK, unit)` continuing as `PCQRec` (`POPClient` mirror). -/
def PCNoopS : SessionType :=
  SessionType.externalChoice "POPServer" [("OK", "unit", PCQRec)]
/-- External offer by `POPServer`: `(OK, unit)` ending in `tEnd` (`POPClient` mirror). -/
def PCQuitS : SessionType :=
  SessionType.externalChoice "POPServer" [("OK", "unit", SessionType.tEnd)]
/-- Internal choice: `(POPServer, LIST, unit)` continuing as `PCListS`; `(POPServer, RETR,
   unit)` continuing as `PCRetrS`; `(POPServer, DELE, unit)` continuing as `PCDeleS`;
   `(POPServer, NOOP, unit)` continuing as `PCNoopS`; `(POPServer, QUIT, unit)` continuing as
   `PCQuitS` (`POPClient` mirror). -/
def PCQSub : SessionType :=
  SessionType.internalChoice
    [("POPServer", "LIST", "unit", PCListS),
     ("POPServer", "RETR", "unit", PCRetrS),
     ("POPServer", "DELE", "unit", PCDeleS),
     ("POPServer", "NOOP", "unit", PCNoopS),
     ("POPServer", "QUIT", "unit", PCQuitS)]
/-- External offer by `POPServer`: `(ERR, unit)` continuing as `PCRec`; `(OK, unit)` continuing
   as `PCQRec` (`POPClient` mirror). -/
def PCPassES : SessionType :=
  SessionType.externalChoice "POPServer"
    [("ERR", "unit", PCRec), ("OK", "unit", PCQRec)]
/-- Internal choice: `(POPServer, PASS, unit)` continuing as `PCPassES` (`POPClient` mirror). -/
def PCPassS : SessionType :=
  SessionType.internalChoice [("POPServer", "PASS", "unit", PCPassES)]
/-- External offer by `POPServer`: `(ERR, unit)` continuing as `PCRec`; `(OK, unit)` continuing
   as `PCPassS` (`POPClient` mirror). -/
def PCUserS : SessionType :=
  SessionType.externalChoice "POPServer"
    [("ERR", "unit", PCRec), ("OK", "unit", PCPassS)]
/-- Internal choice: `(POPServer, USER, unit)` continuing as `PCUserS` (`POPClient` mirror). -/
def PCSub : SessionType :=
  SessionType.internalChoice [("POPServer", "USER", "unit", PCUserS)]

/-- Grafting equation: substituting `PCRec` for `TryLogin` in `PCBody` yields `PCSub`. -/
theorem PCSub_subst :
    substSessionType PCBody "TryLogin" PCRec = PCSub := rfl
/-- Grafting equation: substituting `PCQRec` for `ClientQuery` in `PCQBody` yields `PCQSub`. -/
theorem PCQSub_subst :
    substSessionType PCQBody "ClientQuery" PCQRec = PCQSub := rfl

-- `Has`-false facts (all by decide)
/-- The prune `Has` check for (`POPServer`, `ERR`, `unit`) on `PCRec` is `false` (absent from
   the type). -/
theorem PC_has_Rec_ERR_false :
    pruneFirstInputDeepHas "POPServer" "ERR" "unit" PCRec = false := by decide
/-- The prune `Has` check for (`POPServer`, `ERR`, `unit`) on `PCPassS` is `false` (absent from
   the type). -/
theorem PC_has_PassS_ERR_false :
    pruneFirstInputDeepHas "POPServer" "ERR" "unit" PCPassS = false := by decide
/-- The prune `Has` check for (`POPServer`, `OK`, `unit`) on `PCRec` is `false` (absent from the
   type). -/
theorem PC_has_Rec_OK_false :
    pruneFirstInputDeepHas "POPServer" "OK" "unit" PCRec = false := by decide
/-- The prune `Has` check for (`POPServer`, `OK`, `unit`) on `PCPassS` is `false` (absent from
   the type). -/
theorem PC_has_PassS_OK_false :
    pruneFirstInputDeepHas "POPServer" "OK" "unit" PCPassS = false := by decide
/-- The prune `Has` check for (`POPServer`, `MSGS`, `unit`) on `PCQRec` is `false` (absent from
   the type). -/
theorem PC_has_QRec_MSGS_false :
    pruneFirstInputDeepHas "POPServer" "MSGS" "unit" PCQRec = false := by decide
/-- The prune `Has` check for (`POPServer`, `MSGS`, `unit`) on `PCRetrS` is `false` (absent from
   the type). -/
theorem PC_has_RetrS_MSGS_false :
    pruneFirstInputDeepHas "POPServer" "MSGS" "unit" PCRetrS = false := by decide
/-- The prune `Has` check for (`POPServer`, `MSGS`, `unit`) on `PCDeleS` is `false` (absent from
   the type). -/
theorem PC_has_DeleS_MSGS_false :
    pruneFirstInputDeepHas "POPServer" "MSGS" "unit" PCDeleS = false := by decide
/-- The prune `Has` check for (`POPServer`, `MSGS`, `unit`) on `PCNoopS` is `false` (absent from
   the type). -/
theorem PC_has_NoopS_MSGS_false :
    pruneFirstInputDeepHas "POPServer" "MSGS" "unit" PCNoopS = false := by decide
/-- The prune `Has` check for (`POPServer`, `MSGS`, `unit`) on `PCQuitS` is `false` (absent from
   the type). -/
theorem PC_has_QuitS_MSGS_false :
    pruneFirstInputDeepHas "POPServer" "MSGS" "unit" PCQuitS = false := by decide
/-- The prune `Has` check for (`POPServer`, `OK`, `unit`) on `PCListS` is `false` (absent from
   the type). -/
theorem PC_has_ListS_OK_false :
    pruneFirstInputDeepHas "POPServer" "OK" "unit" PCListS = false := by decide
/-- The prune `Has` check for (`POPServer`, `OK`, `unit`) on `PCQRec` is `false` (absent from
   the type). -/
theorem PC_has_QRec_OK_false :
    pruneFirstInputDeepHas "POPServer" "OK" "unit" PCQRec = false := by decide
/-- The prune `Has` check for (`POPServer`, `ERR`, `unit`) on `PCListS` is `false` (absent from
   the type). -/
theorem PC_has_ListS_ERR_false :
    pruneFirstInputDeepHas "POPServer" "ERR" "unit" PCListS = false := by decide
/-- The prune `Has` check for (`POPServer`, `ERR`, `unit`) on `PCNoopS` is `false` (absent from
   the type). -/
theorem PC_has_NoopS_ERR_false :
    pruneFirstInputDeepHas "POPServer" "ERR" "unit" PCNoopS = false := by decide
/-- The prune `Has` check for (`POPServer`, `ERR`, `unit`) on `PCQuitS` is `false` (absent from
   the type). -/
theorem PC_has_QuitS_ERR_false :
    pruneFirstInputDeepHas "POPServer" "ERR" "unit" PCQuitS = false := by decide

-- FA facts about the grafted outer body
/-- One-message prunability of `PCSub` for (`POPServer`, `ERR`, `unit`). -/
theorem FA_PCSub_ERR : PrunableOneMsg "POPServer" "ERR" "unit" PCSub := by
  apply prunable_one_msg_intC_of_step _ "POPServer" "ERR" "unit"
  intro V hS
  cases hS with
  | @intC _ x hmem hHas =>
    obtain ⟨r, l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
    show PrunableOneMsg "POPServer" "ERR" "unit" PCUserS
    apply prunable_one_msg_extC_of_step "POPServer" _ "POPServer" "ERR" "unit"
    intro W hS2
    cases hS2 with
    | @extCQ _ _ y _ hmem2 hHas2 =>
      obtain ⟨l2, s2, U2⟩ := y
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
      rcases hmem2 with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · have h2 : pruneFirstInputDeepHas "POPServer" "ERR" "unit" PCRec = true := hHas2
        rw [PC_has_Rec_ERR_false] at h2
        cases h2
      · have h2 : pruneFirstInputDeepHas "POPServer" "ERR" "unit" PCPassS = true := hHas2
        rw [PC_has_PassS_ERR_false] at h2
        cases h2
/-- One-message prunability of `PCSub` for (`POPServer`, `OK`, `unit`). -/
theorem FA_PCSub_OK : PrunableOneMsg "POPServer" "OK" "unit" PCSub := by
  apply prunable_one_msg_intC_of_step _ "POPServer" "OK" "unit"
  intro V hS
  cases hS with
  | @intC _ x hmem hHas =>
    obtain ⟨r, l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
    show PrunableOneMsg "POPServer" "OK" "unit" PCUserS
    apply prunable_one_msg_extC_of_step "POPServer" _ "POPServer" "OK" "unit"
    intro W hS2
    cases hS2 with
    | @extCQ _ _ y _ hmem2 hHas2 =>
      obtain ⟨l2, s2, U2⟩ := y
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
      rcases hmem2 with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · have h2 : pruneFirstInputDeepHas "POPServer" "OK" "unit" PCRec = true := hHas2
        rw [PC_has_Rec_OK_false] at h2
        cases h2
      · have h2 : pruneFirstInputDeepHas "POPServer" "OK" "unit" PCPassS = true := hHas2
        rw [PC_has_PassS_OK_false] at h2
        cases h2

-- Lift to the outer rec
/-- One-message prunability of `PCRec` for (`POPServer`, `ERR`, `unit`). -/
theorem FA_PCRec_ERR : PrunableOneMsg "POPServer" "ERR" "unit" PCRec :=
  prunable_one_msg_trec_of_succ "POPServer" "ERR" "unit" FA_PCSub_ERR
/-- One-message prunability of `PCRec` for (`POPServer`, `OK`, `unit`). -/
theorem FA_PCRec_OK : PrunableOneMsg "POPServer" "OK" "unit" PCRec :=
  prunable_one_msg_trec_of_succ "POPServer" "OK" "unit" FA_PCSub_OK

-- FA facts about the grafted inner body
/-- One-message prunability of `PCQSub` for (`POPServer`, `MSGS`, `unit`). -/
theorem FA_PCQSub_MSGS : PrunableOneMsg "POPServer" "MSGS" "unit" PCQSub := by
  apply prunable_one_msg_intC_of_step _ "POPServer" "MSGS" "unit"
  intro V hS
  cases hS with
  | @intC _ x hmem hHas =>
    obtain ⟨r, l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · show PrunableOneMsg "POPServer" "MSGS" "unit" PCListS
      apply prunable_one_msg_extC_of_step "POPServer" _ "POPServer" "MSGS" "unit"
      intro W hS2
      cases hS2 with
      | @extCQ _ _ y _ hmem2 hHas2 =>
        obtain ⟨l2, s2, U2⟩ := y
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
        obtain ⟨rfl, rfl, rfl⟩ := hmem2
        have h2 : pruneFirstInputDeepHas "POPServer" "MSGS" "unit" PCQRec = true := hHas2
        rw [PC_has_QRec_MSGS_false] at h2
        cases h2
    · have hR : pruneFirstInputDeepHas "POPServer" "MSGS" "unit" PCRetrS = true := hHas
      rw [PC_has_RetrS_MSGS_false] at hR
      cases hR
    · have hD : pruneFirstInputDeepHas "POPServer" "MSGS" "unit" PCDeleS = true := hHas
      rw [PC_has_DeleS_MSGS_false] at hD
      cases hD
    · have hN : pruneFirstInputDeepHas "POPServer" "MSGS" "unit" PCNoopS = true := hHas
      rw [PC_has_NoopS_MSGS_false] at hN
      cases hN
    · have hQ : pruneFirstInputDeepHas "POPServer" "MSGS" "unit" PCQuitS = true := hHas
      rw [PC_has_QuitS_MSGS_false] at hQ
      cases hQ
/-- One-message prunability of `PCQSub` for (`POPServer`, `OK`, `unit`). -/
theorem FA_PCQSub_OK : PrunableOneMsg "POPServer" "OK" "unit" PCQSub := by
  apply prunable_one_msg_intC_of_step _ "POPServer" "OK" "unit"
  intro V hS
  cases hS with
  | @intC _ x hmem hHas =>
    obtain ⟨r, l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · have hL : pruneFirstInputDeepHas "POPServer" "OK" "unit" PCListS = true := hHas
      rw [PC_has_ListS_OK_false] at hL
      cases hL
    · show PrunableOneMsg "POPServer" "OK" "unit" PCRetrS
      apply prunable_one_msg_extC_of_step "POPServer" _ "POPServer" "OK" "unit"
      intro W hS2
      cases hS2 with
      | @extCQ _ _ y _ hmem2 hHas2 =>
        obtain ⟨l2, s2, U2⟩ := y
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
        rcases hmem2 with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
        · have h2 : pruneFirstInputDeepHas "POPServer" "OK" "unit" PCQRec = true := hHas2
          rw [PC_has_QRec_OK_false] at h2
          cases h2
        · have h2 : pruneFirstInputDeepHas "POPServer" "OK" "unit" PCQRec = true := hHas2
          rw [PC_has_QRec_OK_false] at h2
          cases h2
    · show PrunableOneMsg "POPServer" "OK" "unit" PCDeleS
      apply prunable_one_msg_extC_of_step "POPServer" _ "POPServer" "OK" "unit"
      intro W hS2
      cases hS2 with
      | @extCQ _ _ y _ hmem2 hHas2 =>
        obtain ⟨l2, s2, U2⟩ := y
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
        rcases hmem2 with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
        · have h2 : pruneFirstInputDeepHas "POPServer" "OK" "unit" PCQRec = true := hHas2
          rw [PC_has_QRec_OK_false] at h2
          cases h2
        · have h2 : pruneFirstInputDeepHas "POPServer" "OK" "unit" PCQRec = true := hHas2
          rw [PC_has_QRec_OK_false] at h2
          cases h2
    · show PrunableOneMsg "POPServer" "OK" "unit" PCNoopS
      apply prunable_one_msg_extC_of_step "POPServer" _ "POPServer" "OK" "unit"
      intro W hS2
      cases hS2 with
      | @extCQ _ _ y _ hmem2 hHas2 =>
        obtain ⟨l2, s2, U2⟩ := y
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
        obtain ⟨rfl, rfl, rfl⟩ := hmem2
        have h2 : pruneFirstInputDeepHas "POPServer" "OK" "unit" PCQRec = true := hHas2
        rw [PC_has_QRec_OK_false] at h2
        cases h2
    · show PrunableOneMsg "POPServer" "OK" "unit" PCQuitS
      apply prunable_one_msg_extC_of_step "POPServer" _ "POPServer" "OK" "unit"
      intro W hS2
      cases hS2 with
      | @extCQ _ _ y _ hmem2 hHas2 =>
        obtain ⟨l2, s2, U2⟩ := y
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
        obtain ⟨rfl, rfl, rfl⟩ := hmem2
        exact prunable_one_msg_end _ _ _
/-- One-message prunability of `PCQSub` for (`POPServer`, `ERR`, `unit`). -/
theorem FA_PCQSub_ERR : PrunableOneMsg "POPServer" "ERR" "unit" PCQSub := by
  apply prunable_one_msg_intC_of_step _ "POPServer" "ERR" "unit"
  intro V hS
  cases hS with
  | @intC _ x hmem hHas =>
    obtain ⟨r, l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · have hL : pruneFirstInputDeepHas "POPServer" "ERR" "unit" PCListS = true := hHas
      rw [PC_has_ListS_ERR_false] at hL
      cases hL
    · show PrunableOneMsg "POPServer" "ERR" "unit" PCRetrS
      apply prunable_one_msg_extC_of_step "POPServer" _ "POPServer" "ERR" "unit"
      intro W hS2
      cases hS2 with
      | @extCQ _ _ y _ hmem2 hHas2 =>
        obtain ⟨l2, s2, U2⟩ := y
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
        rcases hmem2 with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
        · have h2 : pruneFirstInputDeepHas "POPServer" "ERR" "unit" PCQRec = true := hHas2
          have hF : pruneFirstInputDeepHas "POPServer" "ERR" "unit" PCQRec = false := by decide
          rw [hF] at h2
          cases h2
        · have h2 : pruneFirstInputDeepHas "POPServer" "ERR" "unit" PCQRec = true := hHas2
          have hF : pruneFirstInputDeepHas "POPServer" "ERR" "unit" PCQRec = false := by decide
          rw [hF] at h2
          cases h2
    · show PrunableOneMsg "POPServer" "ERR" "unit" PCDeleS
      apply prunable_one_msg_extC_of_step "POPServer" _ "POPServer" "ERR" "unit"
      intro W hS2
      cases hS2 with
      | @extCQ _ _ y _ hmem2 hHas2 =>
        obtain ⟨l2, s2, U2⟩ := y
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
        rcases hmem2 with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
        · have h2 : pruneFirstInputDeepHas "POPServer" "ERR" "unit" PCQRec = true := hHas2
          have hF : pruneFirstInputDeepHas "POPServer" "ERR" "unit" PCQRec = false := by decide
          rw [hF] at h2
          cases h2
        · have h2 : pruneFirstInputDeepHas "POPServer" "ERR" "unit" PCQRec = true := hHas2
          have hF : pruneFirstInputDeepHas "POPServer" "ERR" "unit" PCQRec = false := by decide
          rw [hF] at h2
          cases h2
    · have hN : pruneFirstInputDeepHas "POPServer" "ERR" "unit" PCNoopS = true := hHas
      rw [PC_has_NoopS_ERR_false] at hN
      cases hN
    · have hQ : pruneFirstInputDeepHas "POPServer" "ERR" "unit" PCQuitS = true := hHas
      rw [PC_has_QuitS_ERR_false] at hQ
      cases hQ

-- Lift to the inner rec
/-- One-message prunability of `PCQRec` for (`POPServer`, `MSGS`, `unit`). -/
theorem FA_PCQRec_MSGS : PrunableOneMsg "POPServer" "MSGS" "unit" PCQRec :=
  prunable_one_msg_trec_of_succ "POPServer" "MSGS" "unit" FA_PCQSub_MSGS
/-- One-message prunability of `PCQRec` for (`POPServer`, `OK`, `unit`). -/
theorem FA_PCQRec_OK : PrunableOneMsg "POPServer" "OK" "unit" PCQRec :=
  prunable_one_msg_trec_of_succ "POPServer" "OK" "unit" FA_PCQSub_OK
/-- One-message prunability of `PCQRec` for (`POPServer`, `ERR`, `unit`). -/
theorem FA_PCQRec_ERR : PrunableOneMsg "POPServer" "ERR" "unit" PCQRec :=
  prunable_one_msg_trec_of_succ "POPServer" "ERR" "unit" FA_PCQSub_ERR

/-- The prune `Has` check for (`POPServer`, `MSGS`, `unit`) on `PCUserS` is `false` (absent from
   the type). -/
theorem PC_has_UserS_MSGS_false :
    pruneFirstInputDeepHas "POPServer" "MSGS" "unit" PCUserS = false := by decide
/-- One-message prunability of `PCSub` for (`POPServer`, `MSGS`, `unit`). -/
theorem FA_PCSub_MSGS : PrunableOneMsg "POPServer" "MSGS" "unit" PCSub := by
  apply prunable_one_msg_intC_of_step _ "POPServer" "MSGS" "unit"
  intro V hS
  cases hS with
  | @intC _ x hmem hHas =>
    obtain ⟨r, l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
    have hU : pruneFirstInputDeepHas "POPServer" "MSGS" "unit" PCUserS = true := hHas
    rw [PC_has_UserS_MSGS_false] at hU
    cases hU
/-- One-message prunability of `PCRec` for (`POPServer`, `MSGS`, `unit`). -/
theorem FA_PCRec_MSGS : PrunableOneMsg "POPServer" "MSGS" "unit" PCRec :=
  prunable_one_msg_trec_of_succ "POPServer" "MSGS" "unit" FA_PCSub_MSGS

/-- One-message prunability fact. -/
theorem hfaPCQRec : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
    ExposedFrom PCQRec pm lab0 S0 → PrunableOneMsg pm lab0 S0 PCQRec := by
  intro pm lab0 S0 hexp
  cases hexp with
  | trec hsub =>
    cases hsub with
    | intC_step hmem hne hsub2 =>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
      rcases hmem with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
      · cases hsub2 with
        | extC_here hmem2 =>
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
          obtain ⟨rfl, rfl, rfl⟩ := hmem2
          exact FA_PCQRec_MSGS
        | extC_step hne2 hmem2 hsub3 =>
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
          obtain ⟨rfl, rfl, rfl⟩ := hmem2
          cases hsub3
      · cases hsub2 with
        | extC_here hmem2 =>
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
          rcases hmem2 with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
          · exact FA_PCQRec_OK
          · exact FA_PCQRec_ERR
        | extC_step hne2 hmem2 hsub3 =>
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
          rcases hmem2 with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
          · cases hsub3
          · cases hsub3
      · cases hsub2 with
        | extC_here hmem2 =>
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
          rcases hmem2 with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
          · exact FA_PCQRec_OK
          · exact FA_PCQRec_ERR
        | extC_step hne2 hmem2 hsub3 =>
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
          rcases hmem2 with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
          · cases hsub3
          · cases hsub3
      · cases hsub2 with
        | extC_here hmem2 =>
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
          obtain ⟨rfl, rfl, rfl⟩ := hmem2
          exact FA_PCQRec_OK
        | extC_step hne2 hmem2 hsub3 =>
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
          obtain ⟨rfl, rfl, rfl⟩ := hmem2
          cases hsub3
      · cases hsub2 with
        | extC_here hmem2 =>
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
          obtain ⟨rfl, rfl, rfl⟩ := hmem2
          exact FA_PCQRec_OK
        | extC_step hne2 hmem2 hsub3 =>
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
          obtain ⟨rfl, rfl, rfl⟩ := hmem2
          cases hsub3

/-- One-message prunability fact. -/
theorem hfaPCRec : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
    ExposedFrom PCRec pm lab0 S0 → PrunableOneMsg pm lab0 S0 PCRec := by
  intro pm lab0 S0 hexp
  cases hexp with
  | trec hsub =>
    cases hsub with
    | intC_step hmem hne hsub2 =>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
      cases hsub2 with
      | extC_here hmem2 =>
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
        rcases hmem2 with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
        · exact FA_PCRec_ERR
        · exact FA_PCRec_OK
      | extC_step hne2 hmem2 hsub3 =>
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
        rcases hmem2 with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
        · cases hsub3
        · cases hsub3 with
          | intC_step hmem3 hne3 hsub4 =>
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem3
            obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem3
            cases hsub4 with
            | extC_here hmem4 =>
              simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem4
              rcases hmem4 with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
              · exact FA_PCRec_ERR
              · exact FA_PCRec_OK
            | extC_step hne4 hmem4 hsub5 =>
              simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem4
              rcases hmem4 with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
              · cases hsub5
              · cases hsub5 with
                | trec hsub6 =>
                  cases hsub6 with
                  | intC_step hmem6 hne6 hsub7 =>
                    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem6
                    rcases hmem6 with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
                    · cases hsub7 with
                      | extC_here hmem7 =>
                        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem7
                        obtain ⟨rfl, rfl, rfl⟩ := hmem7
                        exact FA_PCRec_MSGS
                      | extC_step hne7 hmem7 hsub8 =>
                        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem7
                        obtain ⟨rfl, rfl, rfl⟩ := hmem7
                        cases hsub8
                    · cases hsub7 with
                      | extC_here hmem7 =>
                        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem7
                        rcases hmem7 with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
                        · exact FA_PCRec_OK
                        · exact FA_PCRec_ERR
                      | extC_step hne7 hmem7 hsub8 =>
                        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem7
                        rcases hmem7 with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
                        · cases hsub8
                        · cases hsub8
                    · cases hsub7 with
                      | extC_here hmem7 =>
                        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem7
                        rcases hmem7 with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
                        · exact FA_PCRec_OK
                        · exact FA_PCRec_ERR
                      | extC_step hne7 hmem7 hsub8 =>
                        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem7
                        rcases hmem7 with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
                        · cases hsub8
                        · cases hsub8
                    · cases hsub7 with
                      | extC_here hmem7 =>
                        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem7
                        obtain ⟨rfl, rfl, rfl⟩ := hmem7
                        exact FA_PCRec_OK
                      | extC_step hne7 hmem7 hsub8 =>
                        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem7
                        obtain ⟨rfl, rfl, rfl⟩ := hmem7
                        cases hsub8
                    · cases hsub7 with
                      | extC_here hmem7 =>
                        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem7
                        obtain ⟨rfl, rfl, rfl⟩ := hmem7
                        exact FA_PCRec_OK
                      | extC_step hne7 hmem7 hsub8 =>
                        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem7
                        obtain ⟨rfl, rfl, rfl⟩ := hmem7
                        cases hsub8

-- Style-B hfa facts for the grafted chain (hexp ignored; Has threaded down)
/-- One-message prunability fact. -/
theorem hfaPCListS : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
    ExposedFrom PCListS pm lab0 S0 → PrunableOneMsg pm lab0 S0 PCListS := by
  intro pm lab0 S0 _
  apply prunable_one_msg_extC_of_step "POPServer" _ pm lab0 S0
  intro V hS
  cases hS with
  | @extCQ _ _ x _ hmem hHas =>
    obtain ⟨l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    have hE : ExposedFrom PCQRec pm lab0 S0 := has_to_exposed _ _ _ _ hHas
    exact hfaPCQRec _ _ _ hE
/-- One-message prunability fact. -/
theorem hfaPCRetrS : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
    ExposedFrom PCRetrS pm lab0 S0 → PrunableOneMsg pm lab0 S0 PCRetrS := by
  intro pm lab0 S0 _
  apply prunable_one_msg_extC_of_step "POPServer" _ pm lab0 S0
  intro V hS
  cases hS with
  | @extCQ _ _ x _ hmem hHas =>
    obtain ⟨l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · have hE : ExposedFrom PCQRec pm lab0 S0 := has_to_exposed _ _ _ _ hHas
      exact hfaPCQRec _ _ _ hE
    · have hE : ExposedFrom PCQRec pm lab0 S0 := has_to_exposed _ _ _ _ hHas
      exact hfaPCQRec _ _ _ hE
/-- One-message prunability fact. -/
theorem hfaPCDeleS : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
    ExposedFrom PCDeleS pm lab0 S0 → PrunableOneMsg pm lab0 S0 PCDeleS := by
  intro pm lab0 S0 _
  apply prunable_one_msg_extC_of_step "POPServer" _ pm lab0 S0
  intro V hS
  cases hS with
  | @extCQ _ _ x _ hmem hHas =>
    obtain ⟨l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · have hE : ExposedFrom PCQRec pm lab0 S0 := has_to_exposed _ _ _ _ hHas
      exact hfaPCQRec _ _ _ hE
    · have hE : ExposedFrom PCQRec pm lab0 S0 := has_to_exposed _ _ _ _ hHas
      exact hfaPCQRec _ _ _ hE
/-- One-message prunability fact. -/
theorem hfaPCNoopS : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
    ExposedFrom PCNoopS pm lab0 S0 → PrunableOneMsg pm lab0 S0 PCNoopS := by
  intro pm lab0 S0 _
  apply prunable_one_msg_extC_of_step "POPServer" _ pm lab0 S0
  intro V hS
  cases hS with
  | @extCQ _ _ x _ hmem hHas =>
    obtain ⟨l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    have hE : ExposedFrom PCQRec pm lab0 S0 := has_to_exposed _ _ _ _ hHas
    exact hfaPCQRec _ _ _ hE
/-- One-message prunability fact. -/
theorem hfaPCQuitS : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
    ExposedFrom PCQuitS pm lab0 S0 → PrunableOneMsg pm lab0 S0 PCQuitS := by
  intro pm lab0 S0 _
  apply prunable_one_msg_extC_of_step "POPServer" _ pm lab0 S0
  intro V hS
  cases hS with
  | @extCQ _ _ x _ hmem hHas =>
    obtain ⟨l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    exact prunable_one_msg_end _ _ _
/-- One-message prunability fact. -/
theorem hfaPCQSub : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
    ExposedFrom PCQSub pm lab0 S0 → PrunableOneMsg pm lab0 S0 PCQSub := by
  intro pm lab0 S0 _
  apply prunable_one_msg_intC_of_step _ pm lab0 S0
  intro V hS
  cases hS with
  | @intC _ x hmem hHas =>
    obtain ⟨r, l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · have hE : ExposedFrom PCListS pm lab0 S0 := has_to_exposed _ _ _ _ hHas
      exact hfaPCListS _ _ _ hE
    · have hE : ExposedFrom PCRetrS pm lab0 S0 := has_to_exposed _ _ _ _ hHas
      exact hfaPCRetrS _ _ _ hE
    · have hE : ExposedFrom PCDeleS pm lab0 S0 := has_to_exposed _ _ _ _ hHas
      exact hfaPCDeleS _ _ _ hE
    · have hE : ExposedFrom PCNoopS pm lab0 S0 := has_to_exposed _ _ _ _ hHas
      exact hfaPCNoopS _ _ _ hE
    · have hE : ExposedFrom PCQuitS pm lab0 S0 := has_to_exposed _ _ _ _ hHas
      exact hfaPCQuitS _ _ _ hE
/-- One-message prunability fact. -/
theorem hfaPCPassES : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
    ExposedFrom PCPassES pm lab0 S0 → PrunableOneMsg pm lab0 S0 PCPassES := by
  intro pm lab0 S0 _
  apply prunable_one_msg_extC_of_step "POPServer" _ pm lab0 S0
  intro V hS
  cases hS with
  | @extCQ _ _ x _ hmem hHas =>
    obtain ⟨l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · have hE : ExposedFrom PCRec pm lab0 S0 := has_to_exposed _ _ _ _ hHas
      exact hfaPCRec _ _ _ hE
    · have hE : ExposedFrom PCQRec pm lab0 S0 := has_to_exposed _ _ _ _ hHas
      exact hfaPCQRec _ _ _ hE
/-- One-message prunability fact. -/
theorem hfaPCPassS : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
    ExposedFrom PCPassS pm lab0 S0 → PrunableOneMsg pm lab0 S0 PCPassS := by
  intro pm lab0 S0 _
  apply prunable_one_msg_intC_of_step _ pm lab0 S0
  intro V hS
  cases hS with
  | @intC _ x hmem hHas =>
    obtain ⟨r, l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
    have hE : ExposedFrom PCPassES pm lab0 S0 := has_to_exposed _ _ _ _ hHas
    exact hfaPCPassES _ _ _ hE
/-- One-message prunability fact. -/
theorem hfaPCUserS : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
    ExposedFrom PCUserS pm lab0 S0 → PrunableOneMsg pm lab0 S0 PCUserS := by
  intro pm lab0 S0 _
  apply prunable_one_msg_extC_of_step "POPServer" _ pm lab0 S0
  intro V hS
  cases hS with
  | @extCQ _ _ x _ hmem hHas =>
    obtain ⟨l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · have hE : ExposedFrom PCRec pm lab0 S0 := has_to_exposed _ _ _ _ hHas
      exact hfaPCRec _ _ _ hE
    · have hE : ExposedFrom PCPassS pm lab0 S0 := has_to_exposed _ _ _ _ hHas
      exact hfaPCPassS _ _ _ hE
/-- One-message prunability fact. -/
theorem hfaPCSub : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
    ExposedFrom PCSub pm lab0 S0 → PrunableOneMsg pm lab0 S0 PCSub := by
  intro pm lab0 S0 _
  apply prunable_one_msg_intC_of_step _ pm lab0 S0
  intro V hS
  cases hS with
  | @intC _ x hmem hHas =>
    obtain ⟨r, l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
    have hE : ExposedFrom PCUserS pm lab0 S0 := has_to_exposed _ _ _ _ hHas
    exact hfaPCUserS _ _ _ hE

/-- Deep adequacy of `POPClient` with empty seen set. -/
theorem POPClient_deep : Prunable [] POPClient := by
  apply Prunable.trec_new [] "TryLogin" PCBody _ _ hfaPCRec
  · simp
  · have hSub : substSessionType PCBody "TryLogin"
        (SessionType.tRec "TryLogin" PCBody) = PCSub := PCSub_subst
    rw [hSub]
    apply Prunable.intC [PCRec] _ _ hfaPCSub
    intro x hmem
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
    apply Prunable.extC [PCRec] "POPServer" _ _ hfaPCUserS
    intro y hmemY
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmemY
    rcases hmemY with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact Prunable.trec_seen [PCRec] "TryLogin" PCBody
        (List.mem_cons.mpr (Or.inl rfl)) hfaPCRec
    · apply Prunable.intC [PCRec] _ _ hfaPCPassS
      intro z hmemZ
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmemZ
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hmemZ
      apply Prunable.extC [PCRec] "POPServer" _ _ hfaPCPassES
      intro w hmemW
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmemW
      rcases hmemW with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · exact Prunable.trec_seen [PCRec] "TryLogin" PCBody
          (List.mem_cons.mpr (Or.inl rfl)) hfaPCRec
      · apply Prunable.trec_new [PCRec] "ClientQuery" PCQBody _ _ hfaPCQRec
        · intro hcon
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hcon
          injection hcon with hX _
          exact absurd hX (by decide)
        · have hSub2 : substSessionType PCQBody "ClientQuery"
              (SessionType.tRec "ClientQuery" PCQBody) = PCQSub := PCQSub_subst
          rw [hSub2]
          apply Prunable.intC [PCQRec, PCRec] _ _ hfaPCQSub
          intro v hmemV
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmemV
          rcases hmemV with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
          · apply Prunable.extC [PCQRec, PCRec] "POPServer" _ _ hfaPCListS
            intro u hmemU
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmemU
            obtain ⟨rfl, rfl, rfl⟩ := hmemU
            exact Prunable.trec_seen [PCQRec, PCRec] "ClientQuery" PCQBody
              (List.mem_cons.mpr (Or.inl rfl)) hfaPCQRec
          · apply Prunable.extC [PCQRec, PCRec] "POPServer" _ _ hfaPCRetrS
            intro u hmemU
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmemU
            rcases hmemU with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
            · exact Prunable.trec_seen [PCQRec, PCRec] "ClientQuery" PCQBody
                (List.mem_cons.mpr (Or.inl rfl)) hfaPCQRec
            · exact Prunable.trec_seen [PCQRec, PCRec] "ClientQuery" PCQBody
                (List.mem_cons.mpr (Or.inl rfl)) hfaPCQRec
          · apply Prunable.extC [PCQRec, PCRec] "POPServer" _ _ hfaPCDeleS
            intro u hmemU
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmemU
            rcases hmemU with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
            · exact Prunable.trec_seen [PCQRec, PCRec] "ClientQuery" PCQBody
                (List.mem_cons.mpr (Or.inl rfl)) hfaPCQRec
            · exact Prunable.trec_seen [PCQRec, PCRec] "ClientQuery" PCQBody
                (List.mem_cons.mpr (Or.inl rfl)) hfaPCQRec
          · apply Prunable.extC [PCQRec, PCRec] "POPServer" _ _ hfaPCNoopS
            intro u hmemU
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmemU
            obtain ⟨rfl, rfl, rfl⟩ := hmemU
            exact Prunable.trec_seen [PCQRec, PCRec] "ClientQuery" PCQBody
              (List.mem_cons.mpr (Or.inl rfl)) hfaPCQRec
          · apply Prunable.extC [PCQRec, PCRec] "POPServer" _ _ hfaPCQuitS
            intro u hmemU
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmemU
            obtain ⟨rfl, rfl, rfl⟩ := hmemU
            exact Prunable.tEnd [PCQRec, PCRec]

/-- Monitorability of `POPClient` (finite prune closure). -/
theorem POPClient_mon : Drainability.Monitorable POPClient := by
  apply Monitorable_of_closed_set POPClient
    {POPClient, PCRec, PCSub, PCUserS, PCPassS, PCPassES, PCQRec, PCQSub,
     PCListS, PCRetrS, PCDeleS, PCNoopS, PCQuitS,
     SessionType.tEnd, SessionType.tVar "TryLogin", SessionType.tVar "ClientQuery"}
  · simp
  · intro U hU V hStep
    simp only [Finset.mem_insert, Finset.mem_singleton] at hU
    rcases hU with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · cases hStep with
      | trec =>
        show PCSub ∈ ({POPClient, PCRec, PCSub, PCUserS, PCPassS, PCPassES, PCQRec, PCQSub,
          PCListS, PCRetrS, PCDeleS, PCNoopS, PCQuitS,
          SessionType.tEnd, SessionType.tVar "TryLogin", SessionType.tVar "ClientQuery"} : Finset SessionType)
        simp
    · cases hStep with
      | trec =>
        show PCSub ∈ ({POPClient, PCRec, PCSub, PCUserS, PCPassS, PCPassES, PCQRec, PCQSub,
          PCListS, PCRetrS, PCDeleS, PCNoopS, PCQuitS,
          SessionType.tEnd, SessionType.tVar "TryLogin", SessionType.tVar "ClientQuery"} : Finset SessionType)
        simp
    · cases hStep with
      | intC hmem =>
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
        simp
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
      | extC hmem =>
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
        rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
        · simp
        · simp
    · cases hStep with
      | trec =>
        show PCQSub ∈ ({POPClient, PCRec, PCSub, PCUserS, PCPassS, PCPassES, PCQRec, PCQSub,
          PCListS, PCRetrS, PCDeleS, PCNoopS, PCQuitS,
          SessionType.tEnd, SessionType.tVar "TryLogin", SessionType.tVar "ClientQuery"} : Finset SessionType)
        simp
    · cases hStep with
      | intC hmem =>
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
        rcases hmem with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · simp
        · simp
        · simp
        · simp
        · simp
    · cases hStep with
      | extC hmem =>
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
        obtain ⟨rfl, rfl, rfl⟩ := hmem
        simp
    · cases hStep with
      | extC hmem =>
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
        rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
        · simp
        · simp
    · cases hStep with
      | extC hmem =>
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
        rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
        · simp
        · simp
    · cases hStep with
      | extC hmem =>
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
        obtain ⟨rfl, rfl, rfl⟩ := hmem
        simp
    · cases hStep with
      | extC hmem =>
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
        obtain ⟨rfl, rfl, rfl⟩ := hmem
        simp
    · cases hStep
    · cases hStep
    · cases hStep


-- Mirror defs for `POPServer`, outer loop (ungrafted; vars kept)
/-- Internal choice: `(POPClient, MSGS, unit)` looping on `ClientQuery` (`POPServer` mirror). -/
def PSList : SessionType :=
  SessionType.internalChoice
    [("POPClient", "MSGS", "unit", SessionType.tVar "ClientQuery")]
/-- Internal choice: `(POPClient, OK, unit)` looping on `ClientQuery`; `(POPClient, ERR, unit)`
   looping on `ClientQuery` (`POPServer` mirror). -/
def PSRetr : SessionType :=
  SessionType.internalChoice
    [("POPClient", "OK", "unit", SessionType.tVar "ClientQuery"),
     ("POPClient", "ERR", "unit", SessionType.tVar "ClientQuery")]
/-- Internal choice: `(POPClient, OK, unit)` looping on `ClientQuery`; `(POPClient, ERR, unit)`
   looping on `ClientQuery` (`POPServer` mirror). -/
def PSDele : SessionType :=
  SessionType.internalChoice
    [("POPClient", "OK", "unit", SessionType.tVar "ClientQuery"),
     ("POPClient", "ERR", "unit", SessionType.tVar "ClientQuery")]
/-- Internal choice: `(POPClient, OK, unit)` looping on `ClientQuery` (`POPServer` mirror). -/
def PSNoop : SessionType :=
  SessionType.internalChoice
    [("POPClient", "OK", "unit", SessionType.tVar "ClientQuery")]
/-- Internal choice: `(POPClient, OK, unit)` ending in `tEnd` (`POPServer` mirror). -/
def PSQuit : SessionType :=
  SessionType.internalChoice
    [("POPClient", "OK", "unit", SessionType.tEnd)]
/-- External offer by `POPClient`: `(LIST, unit)` continuing as `PSList`; `(RETR, unit)`
   continuing as `PSRetr`; `(DELE, unit)` continuing as `PSDele`; `(NOOP, unit)` continuing as
   `PSNoop`; `(QUIT, unit)` continuing as `PSQuit` (`POPServer` mirror). -/
def PSQBody : SessionType :=
  SessionType.externalChoice "POPClient"
    [("LIST", "unit", PSList),
     ("RETR", "unit", PSRetr),
     ("DELE", "unit", PSDele),
     ("NOOP", "unit", PSNoop),
     ("QUIT", "unit", PSQuit)]
/-- Recursive type: loop on `ClientQuery` with body `PSQBody` (`POPServer` mirror). -/
def PSQRec := SessionType.tRec "ClientQuery" PSQBody
/-- Internal choice: `(POPClient, ERR, unit)` looping on `TryLogin`; `(POPClient, OK, unit)`
   continuing as `PSQRec` (`POPServer` mirror). -/
def PSSpe : SessionType :=
  SessionType.internalChoice
    [("POPClient", "ERR", "unit", SessionType.tVar "TryLogin"),
     ("POPClient", "OK", "unit", PSQRec)]
/-- External offer by `POPClient`: `(PASS, unit)` continuing as `PSSpe` (`POPServer` mirror). -/
def PSSpass : SessionType :=
  SessionType.externalChoice "POPClient" [("PASS", "unit", PSSpe)]
/-- Internal choice: `(POPClient, ERR, unit)` looping on `TryLogin`; `(POPClient, OK, unit)`
   continuing as `PSSpass` (`POPServer` mirror). -/
def PSUser : SessionType :=
  SessionType.internalChoice
    [("POPClient", "ERR", "unit", SessionType.tVar "TryLogin"),
     ("POPClient", "OK", "unit", PSSpass)]
/-- External offer by `POPClient`: `(USER, unit)` continuing as `PSUser` (`POPServer` mirror). -/
def PSBody : SessionType :=
  SessionType.externalChoice "POPClient" [("USER", "unit", PSUser)]
/-- Recursive type: loop on `TryLogin` with body `PSBody` (`POPServer` mirror). -/
def PSRec := SessionType.tRec "TryLogin" PSBody
-- Grafted outer (TryLogin-vars point at the outer rec)
/-- Internal choice: `(POPClient, MSGS, unit)` continuing as `PSQRec` (`POPServer` mirror). -/
def PSListS : SessionType :=
  SessionType.internalChoice [("POPClient", "MSGS", "unit", PSQRec)]
/-- Internal choice: `(POPClient, OK, unit)` continuing as `PSQRec`; `(POPClient, ERR, unit)`
   continuing as `PSQRec` (`POPServer` mirror). -/
def PSRetrS : SessionType :=
  SessionType.internalChoice
    [("POPClient", "OK", "unit", PSQRec), ("POPClient", "ERR", "unit", PSQRec)]
/-- Internal choice: `(POPClient, OK, unit)` continuing as `PSQRec`; `(POPClient, ERR, unit)`
   continuing as `PSQRec` (`POPServer` mirror). -/
def PSDeleS : SessionType :=
  SessionType.internalChoice
    [("POPClient", "OK", "unit", PSQRec), ("POPClient", "ERR", "unit", PSQRec)]
/-- Internal choice: `(POPClient, OK, unit)` continuing as `PSQRec` (`POPServer` mirror). -/
def PSNoopS : SessionType :=
  SessionType.internalChoice [("POPClient", "OK", "unit", PSQRec)]
/-- Internal choice: `(POPClient, OK, unit)` ending in `tEnd` (`POPServer` mirror). -/
def PSQuitS : SessionType :=
  SessionType.internalChoice [("POPClient", "OK", "unit", SessionType.tEnd)]
/-- External offer by `POPClient`: `(LIST, unit)` continuing as `PSListS`; `(RETR, unit)`
   continuing as `PSRetrS`; `(DELE, unit)` continuing as `PSDeleS`; `(NOOP, unit)` continuing as
   `PSNoopS`; `(QUIT, unit)` continuing as `PSQuitS` (`POPServer` mirror). -/
def PSQSub : SessionType :=
  SessionType.externalChoice "POPClient"
    [("LIST", "unit", PSListS),
     ("RETR", "unit", PSRetrS),
     ("DELE", "unit", PSDeleS),
     ("NOOP", "unit", PSNoopS),
     ("QUIT", "unit", PSQuitS)]
/-- Internal choice: `(POPClient, ERR, unit)` continuing as `PSRec`; `(POPClient, OK, unit)`
   continuing as `PSQRec` (`POPServer` mirror). -/
def PSSpeS : SessionType :=
  SessionType.internalChoice
    [("POPClient", "ERR", "unit", PSRec), ("POPClient", "OK", "unit", PSQRec)]
/-- External offer by `POPClient`: `(PASS, unit)` continuing as `PSSpeS` (`POPServer` mirror). -/
def PSSpassS : SessionType :=
  SessionType.externalChoice "POPClient" [("PASS", "unit", PSSpeS)]
/-- Internal choice: `(POPClient, ERR, unit)` continuing as `PSRec`; `(POPClient, OK, unit)`
   continuing as `PSSpassS` (`POPServer` mirror). -/
def PSUserS : SessionType :=
  SessionType.internalChoice
    [("POPClient", "ERR", "unit", PSRec), ("POPClient", "OK", "unit", PSSpassS)]
/-- External offer by `POPClient`: `(USER, unit)` continuing as `PSUserS` (`POPServer` mirror). -/
def PSSub : SessionType :=
  SessionType.externalChoice "POPClient" [("USER", "unit", PSUserS)]

/-- Grafting equation: substituting `PSRec` for `TryLogin` in `PSBody` yields `PSSub`. -/
theorem PSSub_subst :
    substSessionType PSBody "TryLogin" PSRec = PSSub := rfl
/-- Grafting equation: substituting `PSQRec` for `ClientQuery` in `PSQBody` yields `PSQSub`. -/
theorem PSQSub_subst :
    substSessionType PSQBody "ClientQuery" PSQRec = PSQSub := rfl

-- `Has`-false facts (all by decide)
/-- The prune `Has` check for (`POPClient`, `USER`, `unit`) on `PSUserS` is `false` (absent from
   the type). -/
theorem PS_has_User_U_false :
    pruneFirstInputDeepHas "POPClient" "USER" "unit" PSUserS = false := by decide
/-- The prune `Has` check for (`POPClient`, `PASS`, `unit`) on `PSUserS` is `false` (absent from
   the type). -/
theorem PS_has_User_P_false :
    pruneFirstInputDeepHas "POPClient" "PASS" "unit" PSUserS = false := by decide
/-- The prune `Has` check for (`POPClient`, `LIST`, `unit`) on `PSUserS` is `false` (absent from
   the type). -/
theorem PS_has_User_L_false :
    pruneFirstInputDeepHas "POPClient" "LIST" "unit" PSUserS = false := by decide
/-- The prune `Has` check for (`POPClient`, `RETR`, `unit`) on `PSUserS` is `false` (absent from
   the type). -/
theorem PS_has_User_R_false :
    pruneFirstInputDeepHas "POPClient" "RETR" "unit" PSUserS = false := by decide
/-- The prune `Has` check for (`POPClient`, `DELE`, `unit`) on `PSUserS` is `false` (absent from
   the type). -/
theorem PS_has_User_D_false :
    pruneFirstInputDeepHas "POPClient" "DELE" "unit" PSUserS = false := by decide
/-- The prune `Has` check for (`POPClient`, `NOOP`, `unit`) on `PSUserS` is `false` (absent from
   the type). -/
theorem PS_has_User_N_false :
    pruneFirstInputDeepHas "POPClient" "NOOP" "unit" PSUserS = false := by decide
/-- The prune `Has` check for (`POPClient`, `QUIT`, `unit`) on `PSUserS` is `false` (absent from
   the type). -/
theorem PS_has_User_Q_false :
    pruneFirstInputDeepHas "POPClient" "QUIT" "unit" PSUserS = false := by decide
/-- The prune `Has` check for (`POPClient`, `LIST`, `unit`) on `PSListS` is `false` (absent from
   the type). -/
theorem PS_has_List_L_false :
    pruneFirstInputDeepHas "POPClient" "LIST" "unit" PSListS = false := by decide
/-- The prune `Has` check for (`POPClient`, `RETR`, `unit`) on `PSListS` is `false` (absent from
   the type). -/
theorem PS_has_List_R_false :
    pruneFirstInputDeepHas "POPClient" "RETR" "unit" PSListS = false := by decide
/-- The prune `Has` check for (`POPClient`, `DELE`, `unit`) on `PSListS` is `false` (absent from
   the type). -/
theorem PS_has_List_D_false :
    pruneFirstInputDeepHas "POPClient" "DELE" "unit" PSListS = false := by decide
/-- The prune `Has` check for (`POPClient`, `NOOP`, `unit`) on `PSListS` is `false` (absent from
   the type). -/
theorem PS_has_List_N_false :
    pruneFirstInputDeepHas "POPClient" "NOOP" "unit" PSListS = false := by decide
/-- The prune `Has` check for (`POPClient`, `QUIT`, `unit`) on `PSListS` is `false` (absent from
   the type). -/
theorem PS_has_List_Q_false :
    pruneFirstInputDeepHas "POPClient" "QUIT" "unit" PSListS = false := by decide
/-- The prune `Has` check for (`POPClient`, `LIST`, `unit`) on `PSRetrS` is `false` (absent from
   the type). -/
theorem PS_has_Retr_L_false :
    pruneFirstInputDeepHas "POPClient" "LIST" "unit" PSRetrS = false := by decide
/-- The prune `Has` check for (`POPClient`, `RETR`, `unit`) on `PSRetrS` is `false` (absent from
   the type). -/
theorem PS_has_Retr_R_false :
    pruneFirstInputDeepHas "POPClient" "RETR" "unit" PSRetrS = false := by decide
/-- The prune `Has` check for (`POPClient`, `DELE`, `unit`) on `PSRetrS` is `false` (absent from
   the type). -/
theorem PS_has_Retr_D_false :
    pruneFirstInputDeepHas "POPClient" "DELE" "unit" PSRetrS = false := by decide
/-- The prune `Has` check for (`POPClient`, `NOOP`, `unit`) on `PSRetrS` is `false` (absent from
   the type). -/
theorem PS_has_Retr_N_false :
    pruneFirstInputDeepHas "POPClient" "NOOP" "unit" PSRetrS = false := by decide
/-- The prune `Has` check for (`POPClient`, `QUIT`, `unit`) on `PSRetrS` is `false` (absent from
   the type). -/
theorem PS_has_Retr_Q_false :
    pruneFirstInputDeepHas "POPClient" "QUIT" "unit" PSRetrS = false := by decide
/-- The prune `Has` check for (`POPClient`, `LIST`, `unit`) on `PSDeleS` is `false` (absent from
   the type). -/
theorem PS_has_Dele_L_false :
    pruneFirstInputDeepHas "POPClient" "LIST" "unit" PSDeleS = false := by decide
/-- The prune `Has` check for (`POPClient`, `RETR`, `unit`) on `PSDeleS` is `false` (absent from
   the type). -/
theorem PS_has_Dele_R_false :
    pruneFirstInputDeepHas "POPClient" "RETR" "unit" PSDeleS = false := by decide
/-- The prune `Has` check for (`POPClient`, `DELE`, `unit`) on `PSDeleS` is `false` (absent from
   the type). -/
theorem PS_has_Dele_D_false :
    pruneFirstInputDeepHas "POPClient" "DELE" "unit" PSDeleS = false := by decide
/-- The prune `Has` check for (`POPClient`, `NOOP`, `unit`) on `PSDeleS` is `false` (absent from
   the type). -/
theorem PS_has_Dele_N_false :
    pruneFirstInputDeepHas "POPClient" "NOOP" "unit" PSDeleS = false := by decide
/-- The prune `Has` check for (`POPClient`, `QUIT`, `unit`) on `PSDeleS` is `false` (absent from
   the type). -/
theorem PS_has_Dele_Q_false :
    pruneFirstInputDeepHas "POPClient" "QUIT" "unit" PSDeleS = false := by decide
/-- The prune `Has` check for (`POPClient`, `LIST`, `unit`) on `PSNoopS` is `false` (absent from
   the type). -/
theorem PS_has_Noop_L_false :
    pruneFirstInputDeepHas "POPClient" "LIST" "unit" PSNoopS = false := by decide
/-- The prune `Has` check for (`POPClient`, `RETR`, `unit`) on `PSNoopS` is `false` (absent from
   the type). -/
theorem PS_has_Noop_R_false :
    pruneFirstInputDeepHas "POPClient" "RETR" "unit" PSNoopS = false := by decide
/-- The prune `Has` check for (`POPClient`, `DELE`, `unit`) on `PSNoopS` is `false` (absent from
   the type). -/
theorem PS_has_Noop_D_false :
    pruneFirstInputDeepHas "POPClient" "DELE" "unit" PSNoopS = false := by decide
/-- The prune `Has` check for (`POPClient`, `NOOP`, `unit`) on `PSNoopS` is `false` (absent from
   the type). -/
theorem PS_has_Noop_N_false :
    pruneFirstInputDeepHas "POPClient" "NOOP" "unit" PSNoopS = false := by decide
/-- The prune `Has` check for (`POPClient`, `QUIT`, `unit`) on `PSNoopS` is `false` (absent from
   the type). -/
theorem PS_has_Noop_Q_false :
    pruneFirstInputDeepHas "POPClient" "QUIT" "unit" PSNoopS = false := by decide
/-- The prune `Has` check for (`POPClient`, `LIST`, `unit`) on `PSQuitS` is `false` (absent from
   the type). -/
theorem PS_has_Quit_L_false :
    pruneFirstInputDeepHas "POPClient" "LIST" "unit" PSQuitS = false := by decide
/-- The prune `Has` check for (`POPClient`, `RETR`, `unit`) on `PSQuitS` is `false` (absent from
   the type). -/
theorem PS_has_Quit_R_false :
    pruneFirstInputDeepHas "POPClient" "RETR" "unit" PSQuitS = false := by decide
/-- The prune `Has` check for (`POPClient`, `DELE`, `unit`) on `PSQuitS` is `false` (absent from
   the type). -/
theorem PS_has_Quit_D_false :
    pruneFirstInputDeepHas "POPClient" "DELE" "unit" PSQuitS = false := by decide
/-- The prune `Has` check for (`POPClient`, `NOOP`, `unit`) on `PSQuitS` is `false` (absent from
   the type). -/
theorem PS_has_Quit_N_false :
    pruneFirstInputDeepHas "POPClient" "NOOP" "unit" PSQuitS = false := by decide
/-- The prune `Has` check for (`POPClient`, `QUIT`, `unit`) on `PSQuitS` is `false` (absent from
   the type). -/
theorem PS_has_Quit_Q_false :
    pruneFirstInputDeepHas "POPClient" "QUIT" "unit" PSQuitS = false := by decide

-- FA facts about the grafted outer body (single branch, all contra)
/-- One-message prunability of `PSSub` for (`POPClient`, `USER`, `unit`). -/
theorem FA_PSSub_USER : PrunableOneMsg "POPClient" "USER" "unit" PSSub := by
  apply prunable_one_msg_extC_of_step "POPClient" _ "POPClient" "USER" "unit"
  intro V hS
  cases hS with
  | @extCQ _ _ x _ hmem hHas =>
    obtain ⟨l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    have hU : pruneFirstInputDeepHas "POPClient" "USER" "unit" PSUserS = true := hHas
    rw [PS_has_User_U_false] at hU
    cases hU
/-- One-message prunability of `PSSub` for (`POPClient`, `PASS`, `unit`). -/
theorem FA_PSSub_PASS : PrunableOneMsg "POPClient" "PASS" "unit" PSSub := by
  apply prunable_one_msg_extC_of_step "POPClient" _ "POPClient" "PASS" "unit"
  intro V hS
  cases hS with
  | @extCQ _ _ x _ hmem hHas =>
    obtain ⟨l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    have hU : pruneFirstInputDeepHas "POPClient" "PASS" "unit" PSUserS = true := hHas
    rw [PS_has_User_P_false] at hU
    cases hU
/-- One-message prunability of `PSSub` for (`POPClient`, `LIST`, `unit`). -/
theorem FA_PSSub_LIST : PrunableOneMsg "POPClient" "LIST" "unit" PSSub := by
  apply prunable_one_msg_extC_of_step "POPClient" _ "POPClient" "LIST" "unit"
  intro V hS
  cases hS with
  | @extCQ _ _ x _ hmem hHas =>
    obtain ⟨l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    have hU : pruneFirstInputDeepHas "POPClient" "LIST" "unit" PSUserS = true := hHas
    rw [PS_has_User_L_false] at hU
    cases hU
/-- One-message prunability of `PSSub` for (`POPClient`, `RETR`, `unit`). -/
theorem FA_PSSub_RETR : PrunableOneMsg "POPClient" "RETR" "unit" PSSub := by
  apply prunable_one_msg_extC_of_step "POPClient" _ "POPClient" "RETR" "unit"
  intro V hS
  cases hS with
  | @extCQ _ _ x _ hmem hHas =>
    obtain ⟨l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    have hU : pruneFirstInputDeepHas "POPClient" "RETR" "unit" PSUserS = true := hHas
    rw [PS_has_User_R_false] at hU
    cases hU
/-- One-message prunability of `PSSub` for (`POPClient`, `DELE`, `unit`). -/
theorem FA_PSSub_DELE : PrunableOneMsg "POPClient" "DELE" "unit" PSSub := by
  apply prunable_one_msg_extC_of_step "POPClient" _ "POPClient" "DELE" "unit"
  intro V hS
  cases hS with
  | @extCQ _ _ x _ hmem hHas =>
    obtain ⟨l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    have hU : pruneFirstInputDeepHas "POPClient" "DELE" "unit" PSUserS = true := hHas
    rw [PS_has_User_D_false] at hU
    cases hU
/-- One-message prunability of `PSSub` for (`POPClient`, `NOOP`, `unit`). -/
theorem FA_PSSub_NOOP : PrunableOneMsg "POPClient" "NOOP" "unit" PSSub := by
  apply prunable_one_msg_extC_of_step "POPClient" _ "POPClient" "NOOP" "unit"
  intro V hS
  cases hS with
  | @extCQ _ _ x _ hmem hHas =>
    obtain ⟨l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    have hU : pruneFirstInputDeepHas "POPClient" "NOOP" "unit" PSUserS = true := hHas
    rw [PS_has_User_N_false] at hU
    cases hU
/-- One-message prunability of `PSSub` for (`POPClient`, `QUIT`, `unit`). -/
theorem FA_PSSub_QUIT : PrunableOneMsg "POPClient" "QUIT" "unit" PSSub := by
  apply prunable_one_msg_extC_of_step "POPClient" _ "POPClient" "QUIT" "unit"
  intro V hS
  cases hS with
  | @extCQ _ _ x _ hmem hHas =>
    obtain ⟨l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    have hU : pruneFirstInputDeepHas "POPClient" "QUIT" "unit" PSUserS = true := hHas
    rw [PS_has_User_Q_false] at hU
    cases hU

-- Lift to the outer rec
/-- One-message prunability of `PSRec` for (`POPClient`, `USER`, `unit`). -/
theorem FA_PSRec_USER : PrunableOneMsg "POPClient" "USER" "unit" PSRec :=
  prunable_one_msg_trec_of_succ "POPClient" "USER" "unit" FA_PSSub_USER
/-- One-message prunability of `PSRec` for (`POPClient`, `PASS`, `unit`). -/
theorem FA_PSRec_PASS : PrunableOneMsg "POPClient" "PASS" "unit" PSRec :=
  prunable_one_msg_trec_of_succ "POPClient" "PASS" "unit" FA_PSSub_PASS
/-- One-message prunability of `PSRec` for (`POPClient`, `LIST`, `unit`). -/
theorem FA_PSRec_LIST : PrunableOneMsg "POPClient" "LIST" "unit" PSRec :=
  prunable_one_msg_trec_of_succ "POPClient" "LIST" "unit" FA_PSSub_LIST
/-- One-message prunability of `PSRec` for (`POPClient`, `RETR`, `unit`). -/
theorem FA_PSRec_RETR : PrunableOneMsg "POPClient" "RETR" "unit" PSRec :=
  prunable_one_msg_trec_of_succ "POPClient" "RETR" "unit" FA_PSSub_RETR
/-- One-message prunability of `PSRec` for (`POPClient`, `DELE`, `unit`). -/
theorem FA_PSRec_DELE : PrunableOneMsg "POPClient" "DELE" "unit" PSRec :=
  prunable_one_msg_trec_of_succ "POPClient" "DELE" "unit" FA_PSSub_DELE
/-- One-message prunability of `PSRec` for (`POPClient`, `NOOP`, `unit`). -/
theorem FA_PSRec_NOOP : PrunableOneMsg "POPClient" "NOOP" "unit" PSRec :=
  prunable_one_msg_trec_of_succ "POPClient" "NOOP" "unit" FA_PSSub_NOOP
/-- One-message prunability of `PSRec` for (`POPClient`, `QUIT`, `unit`). -/
theorem FA_PSRec_QUIT : PrunableOneMsg "POPClient" "QUIT" "unit" PSRec :=
  prunable_one_msg_trec_of_succ "POPClient" "QUIT" "unit" FA_PSSub_QUIT

-- FA facts about the grafted inner body (5 branches, all contra)
/-- One-message prunability of `PSQSub` for (`POPClient`, `LIST`, `unit`). -/
theorem FA_PSQSub_LIST : PrunableOneMsg "POPClient" "LIST" "unit" PSQSub := by
  apply prunable_one_msg_extC_of_step "POPClient" _ "POPClient" "LIST" "unit"
  intro V hS
  cases hS with
  | @extCQ _ _ x _ hmem hHas =>
    obtain ⟨l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · have hX : pruneFirstInputDeepHas "POPClient" "LIST" "unit" PSListS = true := hHas
      rw [PS_has_List_L_false] at hX
      cases hX
    · have hX : pruneFirstInputDeepHas "POPClient" "LIST" "unit" PSRetrS = true := hHas
      rw [PS_has_Retr_L_false] at hX
      cases hX
    · have hX : pruneFirstInputDeepHas "POPClient" "LIST" "unit" PSDeleS = true := hHas
      rw [PS_has_Dele_L_false] at hX
      cases hX
    · have hX : pruneFirstInputDeepHas "POPClient" "LIST" "unit" PSNoopS = true := hHas
      rw [PS_has_Noop_L_false] at hX
      cases hX
    · have hX : pruneFirstInputDeepHas "POPClient" "LIST" "unit" PSQuitS = true := hHas
      rw [PS_has_Quit_L_false] at hX
      cases hX

/-- One-message prunability of `PSQSub` for (`POPClient`, `RETR`, `unit`). -/
theorem FA_PSQSub_RETR : PrunableOneMsg "POPClient" "RETR" "unit" PSQSub := by
  apply prunable_one_msg_extC_of_step "POPClient" _ "POPClient" "RETR" "unit"
  intro V hS
  cases hS with
  | @extCQ _ _ x _ hmem hHas =>
    obtain ⟨l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · have hX : pruneFirstInputDeepHas "POPClient" "RETR" "unit" PSListS = true := hHas
      rw [PS_has_List_R_false] at hX
      cases hX
    · have hX : pruneFirstInputDeepHas "POPClient" "RETR" "unit" PSRetrS = true := hHas
      rw [PS_has_Retr_R_false] at hX
      cases hX
    · have hX : pruneFirstInputDeepHas "POPClient" "RETR" "unit" PSDeleS = true := hHas
      rw [PS_has_Dele_R_false] at hX
      cases hX
    · have hX : pruneFirstInputDeepHas "POPClient" "RETR" "unit" PSNoopS = true := hHas
      rw [PS_has_Noop_R_false] at hX
      cases hX
    · have hX : pruneFirstInputDeepHas "POPClient" "RETR" "unit" PSQuitS = true := hHas
      rw [PS_has_Quit_R_false] at hX
      cases hX

/-- One-message prunability of `PSQSub` for (`POPClient`, `DELE`, `unit`). -/
theorem FA_PSQSub_DELE : PrunableOneMsg "POPClient" "DELE" "unit" PSQSub := by
  apply prunable_one_msg_extC_of_step "POPClient" _ "POPClient" "DELE" "unit"
  intro V hS
  cases hS with
  | @extCQ _ _ x _ hmem hHas =>
    obtain ⟨l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · have hX : pruneFirstInputDeepHas "POPClient" "DELE" "unit" PSListS = true := hHas
      rw [PS_has_List_D_false] at hX
      cases hX
    · have hX : pruneFirstInputDeepHas "POPClient" "DELE" "unit" PSRetrS = true := hHas
      rw [PS_has_Retr_D_false] at hX
      cases hX
    · have hX : pruneFirstInputDeepHas "POPClient" "DELE" "unit" PSDeleS = true := hHas
      rw [PS_has_Dele_D_false] at hX
      cases hX
    · have hX : pruneFirstInputDeepHas "POPClient" "DELE" "unit" PSNoopS = true := hHas
      rw [PS_has_Noop_D_false] at hX
      cases hX
    · have hX : pruneFirstInputDeepHas "POPClient" "DELE" "unit" PSQuitS = true := hHas
      rw [PS_has_Quit_D_false] at hX
      cases hX

/-- One-message prunability of `PSQSub` for (`POPClient`, `NOOP`, `unit`). -/
theorem FA_PSQSub_NOOP : PrunableOneMsg "POPClient" "NOOP" "unit" PSQSub := by
  apply prunable_one_msg_extC_of_step "POPClient" _ "POPClient" "NOOP" "unit"
  intro V hS
  cases hS with
  | @extCQ _ _ x _ hmem hHas =>
    obtain ⟨l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · have hX : pruneFirstInputDeepHas "POPClient" "NOOP" "unit" PSListS = true := hHas
      rw [PS_has_List_N_false] at hX
      cases hX
    · have hX : pruneFirstInputDeepHas "POPClient" "NOOP" "unit" PSRetrS = true := hHas
      rw [PS_has_Retr_N_false] at hX
      cases hX
    · have hX : pruneFirstInputDeepHas "POPClient" "NOOP" "unit" PSDeleS = true := hHas
      rw [PS_has_Dele_N_false] at hX
      cases hX
    · have hX : pruneFirstInputDeepHas "POPClient" "NOOP" "unit" PSNoopS = true := hHas
      rw [PS_has_Noop_N_false] at hX
      cases hX
    · have hX : pruneFirstInputDeepHas "POPClient" "NOOP" "unit" PSQuitS = true := hHas
      rw [PS_has_Quit_N_false] at hX
      cases hX

/-- One-message prunability of `PSQSub` for (`POPClient`, `QUIT`, `unit`). -/
theorem FA_PSQSub_QUIT : PrunableOneMsg "POPClient" "QUIT" "unit" PSQSub := by
  apply prunable_one_msg_extC_of_step "POPClient" _ "POPClient" "QUIT" "unit"
  intro V hS
  cases hS with
  | @extCQ _ _ x _ hmem hHas =>
    obtain ⟨l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · have hX : pruneFirstInputDeepHas "POPClient" "QUIT" "unit" PSListS = true := hHas
      rw [PS_has_List_Q_false] at hX
      cases hX
    · have hX : pruneFirstInputDeepHas "POPClient" "QUIT" "unit" PSRetrS = true := hHas
      rw [PS_has_Retr_Q_false] at hX
      cases hX
    · have hX : pruneFirstInputDeepHas "POPClient" "QUIT" "unit" PSDeleS = true := hHas
      rw [PS_has_Dele_Q_false] at hX
      cases hX
    · have hX : pruneFirstInputDeepHas "POPClient" "QUIT" "unit" PSNoopS = true := hHas
      rw [PS_has_Noop_Q_false] at hX
      cases hX
    · have hX : pruneFirstInputDeepHas "POPClient" "QUIT" "unit" PSQuitS = true := hHas
      rw [PS_has_Quit_Q_false] at hX
      cases hX

-- Lift to the inner rec
/-- One-message prunability of `PSQRec` for (`POPClient`, `LIST`, `unit`). -/
theorem FA_PSQRec_LIST : PrunableOneMsg "POPClient" "LIST" "unit" PSQRec :=
  prunable_one_msg_trec_of_succ "POPClient" "LIST" "unit" FA_PSQSub_LIST
/-- One-message prunability of `PSQRec` for (`POPClient`, `RETR`, `unit`). -/
theorem FA_PSQRec_RETR : PrunableOneMsg "POPClient" "RETR" "unit" PSQRec :=
  prunable_one_msg_trec_of_succ "POPClient" "RETR" "unit" FA_PSQSub_RETR
/-- One-message prunability of `PSQRec` for (`POPClient`, `DELE`, `unit`). -/
theorem FA_PSQRec_DELE : PrunableOneMsg "POPClient" "DELE" "unit" PSQRec :=
  prunable_one_msg_trec_of_succ "POPClient" "DELE" "unit" FA_PSQSub_DELE
/-- One-message prunability of `PSQRec` for (`POPClient`, `NOOP`, `unit`). -/
theorem FA_PSQRec_NOOP : PrunableOneMsg "POPClient" "NOOP" "unit" PSQRec :=
  prunable_one_msg_trec_of_succ "POPClient" "NOOP" "unit" FA_PSQSub_NOOP
/-- One-message prunability of `PSQRec` for (`POPClient`, `QUIT`, `unit`). -/
theorem FA_PSQRec_QUIT : PrunableOneMsg "POPClient" "QUIT" "unit" PSQRec :=
  prunable_one_msg_trec_of_succ "POPClient" "QUIT" "unit" FA_PSQSub_QUIT

/-- One-message prunability fact. -/
theorem hfaPSQRec : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
    ExposedFrom PSQRec pm lab0 S0 → PrunableOneMsg pm lab0 S0 PSQRec := by
  intro pm lab0 S0 hexp
  cases hexp with
  | trec hsub =>
    cases hsub with
    | extC_here hmem =>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
      rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · exact FA_PSQRec_LIST
      · exact FA_PSQRec_RETR
      · exact FA_PSQRec_DELE
      · exact FA_PSQRec_NOOP
      · exact FA_PSQRec_QUIT
    | extC_step hne hmem hsub2 =>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
      rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · cases hsub2 with
        | intC_step hmem2 hne2 hsub3 =>
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
          obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem2
          cases hsub3
      · cases hsub2 with
        | intC_step hmem2 hne2 hsub3 =>
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
          rcases hmem2 with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
          · cases hsub3
          · cases hsub3
      · cases hsub2 with
        | intC_step hmem2 hne2 hsub3 =>
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
          rcases hmem2 with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
          · cases hsub3
          · cases hsub3
      · cases hsub2 with
        | intC_step hmem2 hne2 hsub3 =>
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
          obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem2
          cases hsub3
      · cases hsub2 with
        | intC_step hmem2 hne2 hsub3 =>
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
          obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem2
          cases hsub3

/-- One-message prunability fact. -/
theorem hfaPSRec : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
    ExposedFrom PSRec pm lab0 S0 → PrunableOneMsg pm lab0 S0 PSRec := by
  intro pm lab0 S0 hexp
  cases hexp with
  | trec hsub =>
    cases hsub with
    | extC_here hmem =>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
      obtain ⟨rfl, rfl, rfl⟩ := hmem
      exact FA_PSRec_USER
    | extC_step hne hmem hsub2 =>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
      obtain ⟨rfl, rfl, rfl⟩ := hmem
      cases hsub2 with
      | intC_step hmem2 hne2 hsub3 =>
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
        rcases hmem2 with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · cases hsub3
        · cases hsub3 with
          | extC_here hmem3 =>
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem3
            obtain ⟨rfl, rfl, rfl⟩ := hmem3
            exact FA_PSRec_PASS
          | extC_step hne3 hmem3 hsub4 =>
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem3
            obtain ⟨rfl, rfl, rfl⟩ := hmem3
            cases hsub4 with
            | intC_step hmem4 hne4 hsub5 =>
              simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem4
              rcases hmem4 with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
              · cases hsub5
              · cases hsub5 with
                | trec hsub6 =>
                  cases hsub6 with
                  | extC_here hmem6 =>
                    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem6
                    rcases hmem6 with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
                    · exact FA_PSRec_LIST
                    · exact FA_PSRec_RETR
                    · exact FA_PSRec_DELE
                    · exact FA_PSRec_NOOP
                    · exact FA_PSRec_QUIT
                  | extC_step hne6 hmem6 hsub7 =>
                    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem6
                    rcases hmem6 with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
                    · cases hsub7 with
                      | intC_step hmem7 hne7 hsub8 =>
                        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem7
                        obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem7
                        cases hsub8
                    · cases hsub7 with
                      | intC_step hmem7 hne7 hsub8 =>
                        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem7
                        rcases hmem7 with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
                        · cases hsub8
                        · cases hsub8
                    · cases hsub7 with
                      | intC_step hmem7 hne7 hsub8 =>
                        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem7
                        rcases hmem7 with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
                        · cases hsub8
                        · cases hsub8
                    · cases hsub7 with
                      | intC_step hmem7 hne7 hsub8 =>
                        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem7
                        obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem7
                        cases hsub8
                    · cases hsub7 with
                      | intC_step hmem7 hne7 hsub8 =>
                        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem7
                        obtain ⟨rfl, rfl, rfl⟩ := hmem7
                        cases hsub8

-- Style-B hfa facts for the grafted chain (hexp ignored; Has threaded down)
/-- One-message prunability fact. -/
theorem hfaPSListS : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
    ExposedFrom PSListS pm lab0 S0 → PrunableOneMsg pm lab0 S0 PSListS := by
  intro pm lab0 S0 _
  apply prunable_one_msg_intC_of_step _ pm lab0 S0
  intro V hS
  cases hS with
  | @intC _ x hmem hHas =>
    obtain ⟨r, l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
    have hE : ExposedFrom PSQRec pm lab0 S0 := has_to_exposed _ _ _ _ hHas
    exact hfaPSQRec _ _ _ hE
/-- One-message prunability fact. -/
theorem hfaPSRetrS : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
    ExposedFrom PSRetrS pm lab0 S0 → PrunableOneMsg pm lab0 S0 PSRetrS := by
  intro pm lab0 S0 _
  apply prunable_one_msg_intC_of_step _ pm lab0 S0
  intro V hS
  cases hS with
  | @intC _ x hmem hHas =>
    obtain ⟨r, l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · have hE : ExposedFrom PSQRec pm lab0 S0 := has_to_exposed _ _ _ _ hHas
      exact hfaPSQRec _ _ _ hE
    · have hE : ExposedFrom PSQRec pm lab0 S0 := has_to_exposed _ _ _ _ hHas
      exact hfaPSQRec _ _ _ hE
/-- One-message prunability fact. -/
theorem hfaPSDeleS : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
    ExposedFrom PSDeleS pm lab0 S0 → PrunableOneMsg pm lab0 S0 PSDeleS := by
  intro pm lab0 S0 _
  apply prunable_one_msg_intC_of_step _ pm lab0 S0
  intro V hS
  cases hS with
  | @intC _ x hmem hHas =>
    obtain ⟨r, l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · have hE : ExposedFrom PSQRec pm lab0 S0 := has_to_exposed _ _ _ _ hHas
      exact hfaPSQRec _ _ _ hE
    · have hE : ExposedFrom PSQRec pm lab0 S0 := has_to_exposed _ _ _ _ hHas
      exact hfaPSQRec _ _ _ hE
/-- One-message prunability fact. -/
theorem hfaPSNoopS : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
    ExposedFrom PSNoopS pm lab0 S0 → PrunableOneMsg pm lab0 S0 PSNoopS := by
  intro pm lab0 S0 _
  apply prunable_one_msg_intC_of_step _ pm lab0 S0
  intro V hS
  cases hS with
  | @intC _ x hmem hHas =>
    obtain ⟨r, l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
    have hE : ExposedFrom PSQRec pm lab0 S0 := has_to_exposed _ _ _ _ hHas
    exact hfaPSQRec _ _ _ hE
/-- One-message prunability fact. -/
theorem hfaPSQuitS : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
    ExposedFrom PSQuitS pm lab0 S0 → PrunableOneMsg pm lab0 S0 PSQuitS := by
  intro pm lab0 S0 _
  apply prunable_one_msg_intC_of_step _ pm lab0 S0
  intro V hS
  cases hS with
  | @intC _ x hmem hHas =>
    obtain ⟨r, l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    exact prunable_one_msg_end _ _ _
/-- One-message prunability fact. -/
theorem hfaPSQSub : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
    ExposedFrom PSQSub pm lab0 S0 → PrunableOneMsg pm lab0 S0 PSQSub := by
  intro pm lab0 S0 _
  apply prunable_one_msg_extC_of_step "POPClient" _ pm lab0 S0
  intro V hS
  cases hS with
  | @extCQ _ _ x _ hmem hHas =>
    obtain ⟨l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · have hE : ExposedFrom PSListS pm lab0 S0 := has_to_exposed _ _ _ _ hHas
      exact hfaPSListS _ _ _ hE
    · have hE : ExposedFrom PSRetrS pm lab0 S0 := has_to_exposed _ _ _ _ hHas
      exact hfaPSRetrS _ _ _ hE
    · have hE : ExposedFrom PSDeleS pm lab0 S0 := has_to_exposed _ _ _ _ hHas
      exact hfaPSDeleS _ _ _ hE
    · have hE : ExposedFrom PSNoopS pm lab0 S0 := has_to_exposed _ _ _ _ hHas
      exact hfaPSNoopS _ _ _ hE
    · have hE : ExposedFrom PSQuitS pm lab0 S0 := has_to_exposed _ _ _ _ hHas
      exact hfaPSQuitS _ _ _ hE
/-- One-message prunability fact. -/
theorem hfaPSSpeS : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
    ExposedFrom PSSpeS pm lab0 S0 → PrunableOneMsg pm lab0 S0 PSSpeS := by
  intro pm lab0 S0 _
  apply prunable_one_msg_intC_of_step _ pm lab0 S0
  intro V hS
  cases hS with
  | @intC _ x hmem hHas =>
    obtain ⟨r, l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · have hE : ExposedFrom PSRec pm lab0 S0 := has_to_exposed _ _ _ _ hHas
      exact hfaPSRec _ _ _ hE
    · have hE : ExposedFrom PSQRec pm lab0 S0 := has_to_exposed _ _ _ _ hHas
      exact hfaPSQRec _ _ _ hE
/-- One-message prunability fact. -/
theorem hfaPSSpassS : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
    ExposedFrom PSSpassS pm lab0 S0 → PrunableOneMsg pm lab0 S0 PSSpassS := by
  intro pm lab0 S0 _
  apply prunable_one_msg_extC_of_step "POPClient" _ pm lab0 S0
  intro V hS
  cases hS with
  | @extCQ _ _ x _ hmem hHas =>
    obtain ⟨l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    have hE : ExposedFrom PSSpeS pm lab0 S0 := has_to_exposed _ _ _ _ hHas
    exact hfaPSSpeS _ _ _ hE
/-- One-message prunability fact. -/
theorem hfaPSUserS : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
    ExposedFrom PSUserS pm lab0 S0 → PrunableOneMsg pm lab0 S0 PSUserS := by
  intro pm lab0 S0 _
  apply prunable_one_msg_intC_of_step _ pm lab0 S0
  intro V hS
  cases hS with
  | @intC _ x hmem hHas =>
    obtain ⟨r, l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · have hE : ExposedFrom PSRec pm lab0 S0 := has_to_exposed _ _ _ _ hHas
      exact hfaPSRec _ _ _ hE
    · have hE : ExposedFrom PSSpassS pm lab0 S0 := has_to_exposed _ _ _ _ hHas
      exact hfaPSSpassS _ _ _ hE
/-- One-message prunability fact. -/
theorem hfaPSSub : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
    ExposedFrom PSSub pm lab0 S0 → PrunableOneMsg pm lab0 S0 PSSub := by
  intro pm lab0 S0 _
  apply prunable_one_msg_extC_of_step "POPClient" _ pm lab0 S0
  intro V hS
  cases hS with
  | @extCQ _ _ x _ hmem hHas =>
    obtain ⟨l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    have hE : ExposedFrom PSUserS pm lab0 S0 := has_to_exposed _ _ _ _ hHas
    exact hfaPSUserS _ _ _ hE

/-- Deep adequacy of `POPServer` with empty seen set. -/
theorem POPServer_deep : Prunable [] POPServer := by
  apply Prunable.trec_new [] "TryLogin" PSBody _ _ hfaPSRec
  · simp
  · have hSub : substSessionType PSBody "TryLogin"
        (SessionType.tRec "TryLogin" PSBody) = PSSub := PSSub_subst
    rw [hSub]
    apply Prunable.extC [PSRec] "POPClient" _ _ hfaPSSub
    intro x hmem
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    apply Prunable.intC [PSRec] _ _ hfaPSUserS
    intro y hmemY
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmemY
    rcases hmemY with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · exact Prunable.trec_seen [PSRec] "TryLogin" PSBody
        (List.mem_cons.mpr (Or.inl rfl)) hfaPSRec
    · apply Prunable.extC [PSRec] "POPClient" _ _ hfaPSSpassS
      intro z hmemZ
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmemZ
      obtain ⟨rfl, rfl, rfl⟩ := hmemZ
      apply Prunable.intC [PSRec] _ _ hfaPSSpeS
      intro w hmemW
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmemW
      rcases hmemW with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
      · exact Prunable.trec_seen [PSRec] "TryLogin" PSBody
          (List.mem_cons.mpr (Or.inl rfl)) hfaPSRec
      · apply Prunable.trec_new [PSRec] "ClientQuery" PSQBody _ _ hfaPSQRec
        · intro hcon
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hcon
          injection hcon with hX _
          exact absurd hX (by decide)
        · have hSub2 : substSessionType PSQBody "ClientQuery"
              (SessionType.tRec "ClientQuery" PSQBody) = PSQSub := PSQSub_subst
          rw [hSub2]
          apply Prunable.extC [PSQRec, PSRec] "POPClient" _ _ hfaPSQSub
          intro v hmemV
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmemV
          rcases hmemV with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
          · apply Prunable.intC [PSQRec, PSRec] _ _ hfaPSListS
            intro u hmemU
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmemU
            obtain ⟨rfl, rfl, rfl, rfl⟩ := hmemU
            exact Prunable.trec_seen [PSQRec, PSRec] "ClientQuery" PSQBody
              (List.mem_cons.mpr (Or.inl rfl)) hfaPSQRec
          · apply Prunable.intC [PSQRec, PSRec] _ _ hfaPSRetrS
            intro u hmemU
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmemU
            rcases hmemU with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
            · exact Prunable.trec_seen [PSQRec, PSRec] "ClientQuery" PSQBody
                (List.mem_cons.mpr (Or.inl rfl)) hfaPSQRec
            · exact Prunable.trec_seen [PSQRec, PSRec] "ClientQuery" PSQBody
                (List.mem_cons.mpr (Or.inl rfl)) hfaPSQRec
          · apply Prunable.intC [PSQRec, PSRec] _ _ hfaPSDeleS
            intro u hmemU
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmemU
            rcases hmemU with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
            · exact Prunable.trec_seen [PSQRec, PSRec] "ClientQuery" PSQBody
                (List.mem_cons.mpr (Or.inl rfl)) hfaPSQRec
            · exact Prunable.trec_seen [PSQRec, PSRec] "ClientQuery" PSQBody
                (List.mem_cons.mpr (Or.inl rfl)) hfaPSQRec
          · apply Prunable.intC [PSQRec, PSRec] _ _ hfaPSNoopS
            intro u hmemU
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmemU
            obtain ⟨rfl, rfl, rfl, rfl⟩ := hmemU
            exact Prunable.trec_seen [PSQRec, PSRec] "ClientQuery" PSQBody
              (List.mem_cons.mpr (Or.inl rfl)) hfaPSQRec
          · apply Prunable.intC [PSQRec, PSRec] _ _ hfaPSQuitS
            intro u hmemU
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmemU
            obtain ⟨rfl, rfl, rfl, rfl⟩ := hmemU
            exact Prunable.tEnd [PSQRec, PSRec]

/-- Monitorability of `POPServer` (finite prune closure). -/
theorem POPServer_mon : Drainability.Monitorable POPServer := by
  apply Monitorable_of_closed_set POPServer
    {POPServer, PSRec, PSSub, PSUserS, PSSpassS, PSSpeS, PSQRec, PSQSub,
     PSListS, PSRetrS, PSDeleS, PSNoopS, PSQuitS,
     SessionType.tEnd, SessionType.tVar "TryLogin", SessionType.tVar "ClientQuery"}
  · simp
  · intro U hU V hStep
    simp only [Finset.mem_insert, Finset.mem_singleton] at hU
    rcases hU with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · cases hStep with
      | trec =>
        show PSSub ∈ ({POPServer, PSRec, PSSub, PSUserS, PSSpassS, PSSpeS, PSQRec, PSQSub,
          PSListS, PSRetrS, PSDeleS, PSNoopS, PSQuitS,
          SessionType.tEnd, SessionType.tVar "TryLogin", SessionType.tVar "ClientQuery"} : Finset SessionType)
        simp
    · cases hStep with
      | trec =>
        show PSSub ∈ ({POPServer, PSRec, PSSub, PSUserS, PSSpassS, PSSpeS, PSQRec, PSQSub,
          PSListS, PSRetrS, PSDeleS, PSNoopS, PSQuitS,
          SessionType.tEnd, SessionType.tVar "TryLogin", SessionType.tVar "ClientQuery"} : Finset SessionType)
        simp
    · cases hStep with
      | extC hmem =>
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
        obtain ⟨rfl, rfl, rfl⟩ := hmem
        simp
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
      | intC hmem =>
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
        rcases hmem with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · simp
        · simp
    · cases hStep with
      | trec =>
        show PSQSub ∈ ({POPServer, PSRec, PSSub, PSUserS, PSSpassS, PSSpeS, PSQRec, PSQSub,
          PSListS, PSRetrS, PSDeleS, PSNoopS, PSQuitS,
          SessionType.tEnd, SessionType.tVar "TryLogin", SessionType.tVar "ClientQuery"} : Finset SessionType)
        simp
    · cases hStep with
      | extC hmem =>
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
        rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
        · simp
        · simp
        · simp
        · simp
        · simp
    · cases hStep with
      | intC hmem =>
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
        simp
    · cases hStep with
      | intC hmem =>
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
        rcases hmem with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · simp
        · simp
    · cases hStep with
      | intC hmem =>
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
        rcases hmem with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · simp
        · simp
    · cases hStep with
      | intC hmem =>
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
        simp
    · cases hStep with
      | intC hmem =>
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
        simp
    · cases hStep
    · cases hStep
    · cases hStep

/-- Empty-queue network for the two POP3 roles. -/
def Net : Network :=
  [("POPClient", (POPClient, [])),
   ("POPServer", (POPServer, []))]

/-- `Net` is well-formed: distinct roles, well-formed types, vacuous sender-closure. -/
theorem Net_wellFormed : Net.WellFormed := by
  refine ⟨by decide, ?_, Network.SenderClosed_of_all_nil (by decide)⟩
  intro x hx
  simp only [Net, List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl
  · exact POPClient.wfCheck_sound (by decide)
  · exact POPServer.wfCheck_sound (by decide)

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
  · simp only [POPClient, rolesOf, rolesOf.goInt, rolesOf.goExt,
      List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmemR
    rcases hmemR with rfl | rfl | hF1 | rfl | rfl | hF2 | (rfl | rfl) | (rfl | rfl) |
      (rfl | rfl) | (rfl | rfl) | rfl | rfl
    · exact ⟨(POPServer, []), by decide⟩
    · exact ⟨(POPServer, []), by decide⟩
    · cases hF1
    · exact ⟨(POPServer, []), by decide⟩
    · exact ⟨(POPServer, []), by decide⟩
    · cases hF2
    · exact ⟨(POPServer, []), by decide⟩
    · exact ⟨(POPServer, []), by decide⟩
    · exact ⟨(POPServer, []), by decide⟩
    · exact ⟨(POPServer, []), by decide⟩
    · exact ⟨(POPServer, []), by decide⟩
    · exact ⟨(POPServer, []), by decide⟩
    · exact ⟨(POPServer, []), by decide⟩
    · exact ⟨(POPServer, []), by decide⟩
    · exact ⟨(POPServer, []), by decide⟩
    · exact ⟨(POPServer, []), by decide⟩
  · simp only [POPServer, rolesOf, rolesOf.goInt, rolesOf.goExt,
      List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmemR
    rcases hmemR with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | (rfl | rfl) |
      (rfl | rfl) | rfl | rfl
    · exact ⟨(POPClient, []), by decide⟩
    · exact ⟨(POPClient, []), by decide⟩
    · exact ⟨(POPClient, []), by decide⟩
    · exact ⟨(POPClient, []), by decide⟩
    · exact ⟨(POPClient, []), by decide⟩
    · exact ⟨(POPClient, []), by decide⟩
    · exact ⟨(POPClient, []), by decide⟩
    · exact ⟨(POPClient, []), by decide⟩
    · exact ⟨(POPClient, []), by decide⟩
    · exact ⟨(POPClient, []), by decide⟩
    · exact ⟨(POPClient, []), by decide⟩
    · exact ⟨(POPClient, []), by decide⟩
    · exact ⟨(POPClient, []), by decide⟩
    · exact ⟨(POPClient, []), by decide⟩

/-- `Net` admits a consistent coinductive instrumentation (empty queues fold trivially). -/
theorem Net_consistent : ∃ MN, consistentInstrumentation_co Net = some MN :=
  exists_consistentInstrumentation_co_of_all_nil Net (by decide)

-- ============ OUT-step characterizations ============
theorem POPClient_out_iff {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans POPClient (st_label.out "POPServer" lab S) T' →
    (lab = "USER" ∧ S = "unit" ∧ T' = PCUserS) := by
  intro h
  unfold POPClient at h
  cases h with
  | tRec hsub =>
    have h2 : st_trans PCSub (st_label.out "POPServer" lab S) T' := hsub
    unfold PCSub at h2
    cases h2 with
    | intC hmem =>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
      exact ⟨rfl, rfl, rfl⟩

theorem PCPassS_out_iff {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans PCPassS (st_label.out p lab S) T' →
    p = "POPServer" ∧ lab = "PASS" ∧ S = "unit" ∧ T' = PCPassES := by
  intro h
  unfold PCPassS at h
  cases h with
  | intC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem PCQRec_out_iff {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans PCQRec (st_label.out p lab S) T' →
    (p = "POPServer" ∧ lab = "LIST" ∧ S = "unit" ∧ T' = PCListS) ∨
    (p = "POPServer" ∧ lab = "RETR" ∧ S = "unit" ∧ T' = PCRetrS) ∨
    (p = "POPServer" ∧ lab = "DELE" ∧ S = "unit" ∧ T' = PCDeleS) ∨
    (p = "POPServer" ∧ lab = "NOOP" ∧ S = "unit" ∧ T' = PCNoopS) ∨
    (p = "POPServer" ∧ lab = "QUIT" ∧ S = "unit" ∧ T' = PCQuitS) := by
  intro h
  unfold PCQRec at h
  cases h with
  | tRec hsub =>
    have h2 : st_trans PCQSub (st_label.out p lab S) T' := hsub
    unfold PCQSub at h2
    cases h2 with
    | intC hmem =>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
      rcases hmem with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
      · exact Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl⟩)))

theorem PSUserS_out_iff {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans PSUserS (st_label.out p lab S) T' →
    (p = "POPClient" ∧ lab = "ERR" ∧ S = "unit" ∧ T' = PSRec) ∨
    (p = "POPClient" ∧ lab = "OK" ∧ S = "unit" ∧ T' = PSSpassS) := by
  intro h
  unfold PSUserS at h
  cases h with
  | intC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl, rfl, rfl⟩

theorem PSSpeS_out_iff {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans PSSpeS (st_label.out p lab S) T' →
    (p = "POPClient" ∧ lab = "ERR" ∧ S = "unit" ∧ T' = PSRec) ∨
    (p = "POPClient" ∧ lab = "OK" ∧ S = "unit" ∧ T' = PSQRec) := by
  intro h
  unfold PSSpeS at h
  cases h with
  | intC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl, rfl, rfl⟩

theorem PSListS_out_iff {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans PSListS (st_label.out p lab S) T' →
    p = "POPClient" ∧ lab = "MSGS" ∧ S = "unit" ∧ T' = PSQRec := by
  intro h
  unfold PSListS at h
  cases h with
  | intC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem PSRetrS_out_iff {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans PSRetrS (st_label.out p lab S) T' →
    (p = "POPClient" ∧ lab = "OK" ∧ S = "unit" ∧ T' = PSQRec) ∨
    (p = "POPClient" ∧ lab = "ERR" ∧ S = "unit" ∧ T' = PSQRec) := by
  intro h
  unfold PSRetrS at h
  cases h with
  | intC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl, rfl, rfl⟩

theorem PSDeleS_out_iff {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans PSDeleS (st_label.out p lab S) T' →
    (p = "POPClient" ∧ lab = "OK" ∧ S = "unit" ∧ T' = PSQRec) ∨
    (p = "POPClient" ∧ lab = "ERR" ∧ S = "unit" ∧ T' = PSQRec) := by
  intro h
  unfold PSDeleS at h
  cases h with
  | intC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl, rfl, rfl⟩

theorem PSNoopS_out_iff {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans PSNoopS (st_label.out p lab S) T' →
    p = "POPClient" ∧ lab = "OK" ∧ S = "unit" ∧ T' = PSQRec := by
  intro h
  unfold PSNoopS at h
  cases h with
  | intC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem PSQuitS_out_iff {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans PSQuitS (st_label.out p lab S) T' →
    p = "POPClient" ∧ lab = "OK" ∧ S = "unit" ∧ T' = SessionType.tEnd := by
  intro h
  unfold PSQuitS at h
  cases h with
  | intC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem POPServer_no_out {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType}
    (h : st_trans POPServer (st_label.out p lab S) T') : False := by
  unfold POPServer at h
  cases h with
  | tRec hsub =>
    have h2 : st_trans PSSub (st_label.out p lab S) T' := hsub
    unfold PSSub at h2
    cases h2

theorem PSSpassS_no_out {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType}
    (h : st_trans PSSpassS (st_label.out p lab S) T') : False := by
  unfold PSSpassS at h
  cases h

theorem PSQRec_no_out {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType}
    (h : st_trans PSQRec (st_label.out p lab S) T') : False := by
  unfold PSQRec at h
  cases h with
  | tRec hsub =>
    have h2 : st_trans PSQSub (st_label.out p lab S) T' := hsub
    unfold PSQSub at h2
    cases h2

theorem PCUserS_no_out {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType}
    (h : st_trans PCUserS (st_label.out p lab S) T') : False := by
  unfold PCUserS at h
  cases h

theorem PCPassES_no_out {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType}
    (h : st_trans PCPassES (st_label.out p lab S) T') : False := by
  unfold PCPassES at h
  cases h

theorem PCListS_no_out {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType}
    (h : st_trans PCListS (st_label.out p lab S) T') : False := by
  unfold PCListS at h
  cases h

theorem PCRetrS_no_out {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType}
    (h : st_trans PCRetrS (st_label.out p lab S) T') : False := by
  unfold PCRetrS at h
  cases h

theorem PCDeleS_no_out {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType}
    (h : st_trans PCDeleS (st_label.out p lab S) T') : False := by
  unfold PCDeleS at h
  cases h

theorem PCNoopS_no_out {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType}
    (h : st_trans PCNoopS (st_label.out p lab S) T') : False := by
  unfold PCNoopS at h
  cases h

theorem PCQuitS_no_out {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType}
    (h : st_trans PCQuitS (st_label.out p lab S) T') : False := by
  unfold PCQuitS at h
  cases h

theorem tEnd_no_out {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType}
    (h : st_trans SessionType.tEnd (st_label.out p lab S) T') : False := by
  cases h

-- ============ INP-step characterizations ============
theorem POPClient_no_inp {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType}
    (h : st_trans POPClient (st_label.inp p lab S) T') : False := by
  unfold POPClient at h
  cases h with
  | tRec hsub =>
    have h2 : st_trans PCSub (st_label.inp p lab S) T' := hsub
    unfold PCSub at h2
    cases h2

theorem PCPassS_no_inp {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType}
    (h : st_trans PCPassS (st_label.inp p lab S) T') : False := by
  unfold PCPassS at h
  cases h

theorem PCQRec_no_inp {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType}
    (h : st_trans PCQRec (st_label.inp p lab S) T') : False := by
  unfold PCQRec at h
  cases h with
  | tRec hsub =>
    have h2 : st_trans PCQSub (st_label.inp p lab S) T' := hsub
    unfold PCQSub at h2
    cases h2

theorem PCUserS_inp_iff {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans PCUserS (st_label.inp p lab S) T' →
    (p = "POPServer" ∧ lab = "ERR" ∧ S = "unit" ∧ T' = PCRec) ∨
    (p = "POPServer" ∧ lab = "OK" ∧ S = "unit" ∧ T' = PCPassS) := by
  intro h
  unfold PCUserS at h
  cases h with
  | extC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl, rfl, rfl⟩

theorem PCPassES_inp_iff {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans PCPassES (st_label.inp p lab S) T' →
    (p = "POPServer" ∧ lab = "ERR" ∧ S = "unit" ∧ T' = PCRec) ∨
    (p = "POPServer" ∧ lab = "OK" ∧ S = "unit" ∧ T' = PCQRec) := by
  intro h
  unfold PCPassES at h
  cases h with
  | extC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl, rfl, rfl⟩

theorem PCListS_inp_iff {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans PCListS (st_label.inp p lab S) T' →
    p = "POPServer" ∧ lab = "MSGS" ∧ S = "unit" ∧ T' = PCQRec := by
  intro h
  unfold PCListS at h
  cases h with
  | extC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem PCRetrS_inp_iff {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans PCRetrS (st_label.inp p lab S) T' →
    (p = "POPServer" ∧ lab = "OK" ∧ S = "unit" ∧ T' = PCQRec) ∨
    (p = "POPServer" ∧ lab = "ERR" ∧ S = "unit" ∧ T' = PCQRec) := by
  intro h
  unfold PCRetrS at h
  cases h with
  | extC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl, rfl, rfl⟩

theorem PCDeleS_inp_iff {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans PCDeleS (st_label.inp p lab S) T' →
    (p = "POPServer" ∧ lab = "OK" ∧ S = "unit" ∧ T' = PCQRec) ∨
    (p = "POPServer" ∧ lab = "ERR" ∧ S = "unit" ∧ T' = PCQRec) := by
  intro h
  unfold PCDeleS at h
  cases h with
  | extC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl, rfl, rfl⟩

theorem PCNoopS_inp_iff {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans PCNoopS (st_label.inp p lab S) T' →
    p = "POPServer" ∧ lab = "OK" ∧ S = "unit" ∧ T' = PCQRec := by
  intro h
  unfold PCNoopS at h
  cases h with
  | extC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem PCQuitS_inp_iff {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans PCQuitS (st_label.inp p lab S) T' →
    p = "POPServer" ∧ lab = "OK" ∧ S = "unit" ∧ T' = SessionType.tEnd := by
  intro h
  unfold PCQuitS at h
  cases h with
  | extC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem POPServer_inp_iff {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans POPServer (st_label.inp p lab S) T' →
    (p = "POPClient" ∧ lab = "USER" ∧ S = "unit" ∧ T' = PSUserS) := by
  intro h
  unfold POPServer at h
  cases h with
  | tRec hsub =>
    have h2 : st_trans PSSub (st_label.inp p lab S) T' := hsub
    unfold PSSub at h2
    cases h2 with
    | extC hmem =>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
      obtain ⟨rfl, rfl, rfl⟩ := hmem
      exact ⟨rfl, rfl, rfl, rfl⟩

theorem PSSpassS_inp_iff {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans PSSpassS (st_label.inp p lab S) T' →
    p = "POPClient" ∧ lab = "PASS" ∧ S = "unit" ∧ T' = PSSpeS := by
  intro h
  unfold PSSpassS at h
  cases h with
  | extC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem PSQRec_inp_iff {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans PSQRec (st_label.inp p lab S) T' →
    (p = "POPClient" ∧ lab = "LIST" ∧ S = "unit" ∧ T' = PSListS) ∨
    (p = "POPClient" ∧ lab = "RETR" ∧ S = "unit" ∧ T' = PSRetrS) ∨
    (p = "POPClient" ∧ lab = "DELE" ∧ S = "unit" ∧ T' = PSDeleS) ∨
    (p = "POPClient" ∧ lab = "NOOP" ∧ S = "unit" ∧ T' = PSNoopS) ∨
    (p = "POPClient" ∧ lab = "QUIT" ∧ S = "unit" ∧ T' = PSQuitS) := by
  intro h
  unfold PSQRec at h
  cases h with
  | tRec hsub =>
    have h2 : st_trans PSQSub (st_label.inp p lab S) T' := hsub
    unfold PSQSub at h2
    cases h2 with
    | extC hmem =>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
      rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
      · exact Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl⟩)))

theorem PSUserS_no_inp {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType}
    (h : st_trans PSUserS (st_label.inp p lab S) T') : False := by
  unfold PSUserS at h
  cases h

theorem PSSpeS_no_inp {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType}
    (h : st_trans PSSpeS (st_label.inp p lab S) T') : False := by
  unfold PSSpeS at h
  cases h

theorem PSListS_no_inp {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType}
    (h : st_trans PSListS (st_label.inp p lab S) T') : False := by
  unfold PSListS at h
  cases h

theorem PSRetrS_no_inp {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType}
    (h : st_trans PSRetrS (st_label.inp p lab S) T') : False := by
  unfold PSRetrS at h
  cases h

theorem PSDeleS_no_inp {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType}
    (h : st_trans PSDeleS (st_label.inp p lab S) T') : False := by
  unfold PSDeleS at h
  cases h

theorem PSNoopS_no_inp {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType}
    (h : st_trans PSNoopS (st_label.inp p lab S) T') : False := by
  unfold PSNoopS at h
  cases h

theorem PSQuitS_no_inp {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType}
    (h : st_trans PSQuitS (st_label.inp p lab S) T') : False := by
  unfold PSQuitS at h
  cases h

theorem tEnd_no_inp {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType}
    (h : st_trans SessionType.tEnd (st_label.inp p lab S) T') : False := by
  cases h


-- ============ Reachable states (whole-network enumeration) ============
-- Messages
abbrev mUSER : QueueMessage := QueueMessage.msg "POPClient" "USER" "unit"
abbrev mPASS : QueueMessage := QueueMessage.msg "POPClient" "PASS" "unit"
abbrev mLIST : QueueMessage := QueueMessage.msg "POPClient" "LIST" "unit"
abbrev mRETR : QueueMessage := QueueMessage.msg "POPClient" "RETR" "unit"
abbrev mDELE : QueueMessage := QueueMessage.msg "POPClient" "DELE" "unit"
abbrev mNOOP : QueueMessage := QueueMessage.msg "POPClient" "NOOP" "unit"
abbrev mQUIT : QueueMessage := QueueMessage.msg "POPClient" "QUIT" "unit"
abbrev mERR : QueueMessage := QueueMessage.msg "POPServer" "ERR" "unit"
abbrev mOK : QueueMessage := QueueMessage.msg "POPServer" "OK" "unit"
abbrev mMSGS : QueueMessage := QueueMessage.msg "POPServer" "MSGS" "unit"

def S0 : Network := [("POPClient", (POPClient, [])), ("POPServer", (POPServer, []))]
def S1 : Network := [("POPServer", (POPServer, [mUSER])), ("POPClient", (PCUserS, []))]
def S2 : Network := [("POPServer", (PSUserS, [])), ("POPClient", (PCUserS, []))]
def S3 : Network := [("POPClient", (PCUserS, [mERR])), ("POPServer", (POPServer, []))]
def S4 : Network := [("POPClient", (PCUserS, [mOK])), ("POPServer", (PSSpassS, []))]
def S5 : Network := [("POPClient", (PCPassS, [])), ("POPServer", (PSSpassS, []))]
def S6 : Network := [("POPServer", (PSSpassS, [mPASS])), ("POPClient", (PCPassES, []))]
def S7 : Network := [("POPServer", (PSSpeS, [])), ("POPClient", (PCPassES, []))]
def S8 : Network := [("POPClient", (PCPassES, [mERR])), ("POPServer", (POPServer, []))]
def S9 : Network := [("POPClient", (PCPassES, [mOK])), ("POPServer", (PSQRec, []))]
def S10 : Network := [("POPClient", (PCQRec, [])), ("POPServer", (PSQRec, []))]
def S11 : Network := [("POPServer", (PSQRec, [mLIST])), ("POPClient", (PCListS, []))]
def S12 : Network := [("POPServer", (PSListS, [])), ("POPClient", (PCListS, []))]
def S13 : Network := [("POPClient", (PCListS, [mMSGS])), ("POPServer", (PSQRec, []))]
def S14 : Network := [("POPServer", (PSQRec, [mRETR])), ("POPClient", (PCRetrS, []))]
def S15 : Network := [("POPServer", (PSRetrS, [])), ("POPClient", (PCRetrS, []))]
def S16 : Network := [("POPClient", (PCRetrS, [mOK])), ("POPServer", (PSQRec, []))]
def S17 : Network := [("POPClient", (PCRetrS, [mERR])), ("POPServer", (PSQRec, []))]
def S18 : Network := [("POPServer", (PSQRec, [mDELE])), ("POPClient", (PCDeleS, []))]
def S19 : Network := [("POPServer", (PSDeleS, [])), ("POPClient", (PCDeleS, []))]
def S20 : Network := [("POPClient", (PCDeleS, [mOK])), ("POPServer", (PSQRec, []))]
def S21 : Network := [("POPClient", (PCDeleS, [mERR])), ("POPServer", (PSQRec, []))]
def S22 : Network := [("POPServer", (PSQRec, [mNOOP])), ("POPClient", (PCNoopS, []))]
def S23 : Network := [("POPServer", (PSNoopS, [])), ("POPClient", (PCNoopS, []))]
def S24 : Network := [("POPClient", (PCNoopS, [mOK])), ("POPServer", (PSQRec, []))]
def S25 : Network := [("POPServer", (PSQRec, [mQUIT])), ("POPClient", (PCQuitS, []))]
def S26 : Network := [("POPServer", (PSQuitS, [])), ("POPClient", (PCQuitS, []))]
def S27 : Network := [("POPClient", (PCQuitS, [mOK])), ("POPServer", (SessionType.tEnd, []))]
def S28 : Network := [("POPClient", (SessionType.tEnd, [])), ("POPServer", (SessionType.tEnd, []))]

-- Queue computations
theorem qUSER_USER : Queue.dequeue [mUSER] (QueueMessage.msg "POPClient" "USER" "unit") = some ([] : Queue) := rfl
theorem qPASS_PASS : Queue.dequeue [mPASS] (QueueMessage.msg "POPClient" "PASS" "unit") = some ([] : Queue) := rfl
theorem qLIST_LIST : Queue.dequeue [mLIST] (QueueMessage.msg "POPClient" "LIST" "unit") = some ([] : Queue) := rfl
theorem qRETR_RETR : Queue.dequeue [mRETR] (QueueMessage.msg "POPClient" "RETR" "unit") = some ([] : Queue) := rfl
theorem qDELE_DELE : Queue.dequeue [mDELE] (QueueMessage.msg "POPClient" "DELE" "unit") = some ([] : Queue) := rfl
theorem qNOOP_NOOP : Queue.dequeue [mNOOP] (QueueMessage.msg "POPClient" "NOOP" "unit") = some ([] : Queue) := rfl
theorem qQUIT_QUIT : Queue.dequeue [mQUIT] (QueueMessage.msg "POPClient" "QUIT" "unit") = some ([] : Queue) := rfl
theorem qERR_ERR : Queue.dequeue [mERR] (QueueMessage.msg "POPServer" "ERR" "unit") = some ([] : Queue) := rfl
theorem qOK_OK : Queue.dequeue [mOK] (QueueMessage.msg "POPServer" "OK" "unit") = some ([] : Queue) := rfl
theorem qMSGS_MSGS : Queue.dequeue [mMSGS] (QueueMessage.msg "POPServer" "MSGS" "unit") = some ([] : Queue) := rfl
theorem qERR_OK : Queue.dequeue [mERR] (QueueMessage.msg "POPServer" "OK" "unit") = none := rfl
theorem qERR_MSGS : Queue.dequeue [mERR] (QueueMessage.msg "POPServer" "MSGS" "unit") = none := rfl
theorem qOK_ERR : Queue.dequeue [mOK] (QueueMessage.msg "POPServer" "ERR" "unit") = none := rfl
theorem qOK_MSGS : Queue.dequeue [mOK] (QueueMessage.msg "POPServer" "MSGS" "unit") = none := rfl
theorem qMSGS_OK : Queue.dequeue [mMSGS] (QueueMessage.msg "POPServer" "OK" "unit") = none := rfl
theorem qMSGS_ERR : Queue.dequeue [mMSGS] (QueueMessage.msg "POPServer" "ERR" "unit") = none := rfl
theorem qLIST_RETR : Queue.dequeue [mLIST] (QueueMessage.msg "POPClient" "RETR" "unit") = none := rfl
theorem qLIST_DELE : Queue.dequeue [mLIST] (QueueMessage.msg "POPClient" "DELE" "unit") = none := rfl
theorem qLIST_NOOP : Queue.dequeue [mLIST] (QueueMessage.msg "POPClient" "NOOP" "unit") = none := rfl
theorem qLIST_QUIT : Queue.dequeue [mLIST] (QueueMessage.msg "POPClient" "QUIT" "unit") = none := rfl
theorem qLIST_USER : Queue.dequeue [mLIST] (QueueMessage.msg "POPClient" "USER" "unit") = none := rfl
theorem qLIST_PASS : Queue.dequeue [mLIST] (QueueMessage.msg "POPClient" "PASS" "unit") = none := rfl
theorem qRETR_LIST : Queue.dequeue [mRETR] (QueueMessage.msg "POPClient" "LIST" "unit") = none := rfl
theorem qRETR_DELE : Queue.dequeue [mRETR] (QueueMessage.msg "POPClient" "DELE" "unit") = none := rfl
theorem qRETR_NOOP : Queue.dequeue [mRETR] (QueueMessage.msg "POPClient" "NOOP" "unit") = none := rfl
theorem qRETR_QUIT : Queue.dequeue [mRETR] (QueueMessage.msg "POPClient" "QUIT" "unit") = none := rfl
theorem qRETR_USER : Queue.dequeue [mRETR] (QueueMessage.msg "POPClient" "USER" "unit") = none := rfl
theorem qRETR_PASS : Queue.dequeue [mRETR] (QueueMessage.msg "POPClient" "PASS" "unit") = none := rfl
theorem qDELE_LIST : Queue.dequeue [mDELE] (QueueMessage.msg "POPClient" "LIST" "unit") = none := rfl
theorem qDELE_RETR : Queue.dequeue [mDELE] (QueueMessage.msg "POPClient" "RETR" "unit") = none := rfl
theorem qDELE_NOOP : Queue.dequeue [mDELE] (QueueMessage.msg "POPClient" "NOOP" "unit") = none := rfl
theorem qDELE_QUIT : Queue.dequeue [mDELE] (QueueMessage.msg "POPClient" "QUIT" "unit") = none := rfl
theorem qNOOP_LIST : Queue.dequeue [mNOOP] (QueueMessage.msg "POPClient" "LIST" "unit") = none := rfl
theorem qNOOP_RETR : Queue.dequeue [mNOOP] (QueueMessage.msg "POPClient" "RETR" "unit") = none := rfl
theorem qNOOP_DELE : Queue.dequeue [mNOOP] (QueueMessage.msg "POPClient" "DELE" "unit") = none := rfl
theorem qNOOP_QUIT : Queue.dequeue [mNOOP] (QueueMessage.msg "POPClient" "QUIT" "unit") = none := rfl
theorem qQUIT_LIST : Queue.dequeue [mQUIT] (QueueMessage.msg "POPClient" "LIST" "unit") = none := rfl
theorem qQUIT_RETR : Queue.dequeue [mQUIT] (QueueMessage.msg "POPClient" "RETR" "unit") = none := rfl
theorem qQUIT_DELE : Queue.dequeue [mQUIT] (QueueMessage.msg "POPClient" "DELE" "unit") = none := rfl
theorem qQUIT_NOOP : Queue.dequeue [mQUIT] (QueueMessage.msg "POPClient" "NOOP" "unit") = none := rfl
theorem qUSER_PASS : Queue.dequeue [mUSER] (QueueMessage.msg "POPClient" "PASS" "unit") = none := rfl
theorem qUSER_LIST : Queue.dequeue [mUSER] (QueueMessage.msg "POPClient" "LIST" "unit") = none := rfl
theorem qUSER_RETR : Queue.dequeue [mUSER] (QueueMessage.msg "POPClient" "RETR" "unit") = none := rfl
theorem qPASS_USER : Queue.dequeue [mPASS] (QueueMessage.msg "POPClient" "USER" "unit") = none := rfl
theorem qPASS_LIST : Queue.dequeue [mPASS] (QueueMessage.msg "POPClient" "LIST" "unit") = none := rfl

theorem S0_step : ∀ (δ : net_label) (N' : Network),
    net_trans S0 δ N' → is_internal_net_label δ → N' = S1 := by
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
          have ho := POPClient_out_iff hST
          obtain ⟨rfl, rfl, rfl⟩ := ho
          rfl
    · cases h_send with
      | send hST => exact absurd hST (fun h => POPServer_no_out h)
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
        have hi := POPServer_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qUSER_USER] at hQ
        cases hQ
        rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S1, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => POPServer_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PCUserS_no_out h)
    · exact absurd rfl hne

theorem S2_step : ∀ (δ : net_label) (N' : Network),
    net_trans S2 δ N' → is_internal_net_label δ → N' = S3 ∨ N' = S4 := by
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
          have ho := PSUserS_out_iff hST
          rcases ho with ⟨-, rfl, rfl, rfl⟩ | ⟨-, rfl, rfl, rfl⟩
          · exact Or.inl rfl
          · exact Or.inr rfl
    · cases h_send with
      | send hST => exact absurd hST (fun h => PCUserS_no_out h)
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
        have hi := PCUserS_inp_iff hST
        rcases hi with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · rw [qERR_ERR] at hQ
          cases hQ
          rfl
        · rw [qERR_OK] at hQ
          cases hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S3, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PCUserS_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => POPServer_no_out h)
    · exact absurd rfl hne

theorem S4_step : ∀ (δ : net_label) (N' : Network),
    net_trans S4 δ N' → is_internal_net_label δ → N' = S5 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S4, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PCUserS_inp_iff hST
        rcases hi with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · rw [qOK_ERR] at hQ
          cases hQ
        · rw [qOK_OK] at hQ
          cases hQ
          rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S4, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PCUserS_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PSSpassS_no_out h)
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
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S5, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := PCPassS_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          rfl
    · cases h_send with
      | send hST => exact absurd hST (fun h => PSSpassS_no_out h)
    · exact absurd rfl hne

theorem S6_step : ∀ (δ : net_label) (N' : Network),
    net_trans S6 δ N' → is_internal_net_label δ → N' = S7 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S6, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PSSpassS_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qPASS_PASS] at hQ
        cases hQ
        rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S6, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PSSpassS_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PCPassES_no_out h)
    · exact absurd rfl hne

theorem S7_step : ∀ (δ : net_label) (N' : Network),
    net_trans S7 δ N' → is_internal_net_label δ → N' = S8 ∨ N' = S9 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S7, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S7, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := PSSpeS_out_iff hST
          rcases ho with ⟨-, rfl, rfl, rfl⟩ | ⟨-, rfl, rfl, rfl⟩
          · exact Or.inl rfl
          · exact Or.inr rfl
    · cases h_send with
      | send hST => exact absurd hST (fun h => PCPassES_no_out h)
    · exact absurd rfl hne

theorem S8_step : ∀ (δ : net_label) (N' : Network),
    net_trans S8 δ N' → is_internal_net_label δ → N' = S0 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S8, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PCPassES_inp_iff hST
        rcases hi with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · rw [qERR_ERR] at hQ
          cases hQ
          rfl
        · rw [qERR_OK] at hQ
          cases hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S8, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PCPassES_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => POPServer_no_out h)
    · exact absurd rfl hne

theorem S9_step : ∀ (δ : net_label) (N' : Network),
    net_trans S9 δ N' → is_internal_net_label δ → N' = S10 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S9, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PCPassES_inp_iff hST
        rcases hi with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · rw [qOK_ERR] at hQ
          cases hQ
        · rw [qOK_OK] at hQ
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
      | send hST => exact absurd hST (fun h => PCPassES_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PSQRec_no_out h)
    · exact absurd rfl hne

theorem S10_step : ∀ (δ : net_label) (N' : Network),
    net_trans S10 δ N' → is_internal_net_label δ → N' = S11 ∨ N' = S14 ∨ N' = S18 ∨ N' = S22 ∨ N' = S25 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S10, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S10, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := PCQRec_out_iff hST
          rcases ho with ⟨-, rfl, rfl, rfl⟩ | ⟨-, rfl, rfl, rfl⟩ | ⟨-, rfl, rfl, rfl⟩ | ⟨-, rfl, rfl, rfl⟩ | ⟨-, rfl, rfl, rfl⟩
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (Or.inl rfl))
          · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
    · cases h_send with
      | send hST => exact absurd hST (fun h => PSQRec_no_out h)
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
        have hi := PSQRec_inp_iff hST
        rcases hi with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · rw [qLIST_LIST] at hQ
          cases hQ
          rfl
        · rw [qLIST_RETR] at hQ
          cases hQ
        · rw [qLIST_DELE] at hQ
          cases hQ
        · rw [qLIST_NOOP] at hQ
          cases hQ
        · rw [qLIST_QUIT] at hQ
          cases hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S11, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PSQRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PCListS_no_out h)
    · exact absurd rfl hne

theorem S12_step : ∀ (δ : net_label) (N' : Network),
    net_trans S12 δ N' → is_internal_net_label δ → N' = S13 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S12, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S12, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := PSListS_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          rfl
    · cases h_send with
      | send hST => exact absurd hST (fun h => PCListS_no_out h)
    · exact absurd rfl hne

theorem S13_step : ∀ (δ : net_label) (N' : Network),
    net_trans S13 δ N' → is_internal_net_label δ → N' = S10 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S13, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PCListS_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qMSGS_MSGS] at hQ
        cases hQ
        rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S13, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PCListS_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PSQRec_no_out h)
    · exact absurd rfl hne

theorem S14_step : ∀ (δ : net_label) (N' : Network),
    net_trans S14 δ N' → is_internal_net_label δ → N' = S15 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S14, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PSQRec_inp_iff hST
        rcases hi with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · rw [qRETR_LIST] at hQ
          cases hQ
        · rw [qRETR_RETR] at hQ
          cases hQ
          rfl
        · rw [qRETR_DELE] at hQ
          cases hQ
        · rw [qRETR_NOOP] at hQ
          cases hQ
        · rw [qRETR_QUIT] at hQ
          cases hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S14, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PSQRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PCRetrS_no_out h)
    · exact absurd rfl hne

theorem S15_step : ∀ (δ : net_label) (N' : Network),
    net_trans S15 δ N' → is_internal_net_label δ → N' = S16 ∨ N' = S17 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S15, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S15, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := PSRetrS_out_iff hST
          rcases ho with ⟨-, rfl, rfl, rfl⟩ | ⟨-, rfl, rfl, rfl⟩
          · exact Or.inl rfl
          · exact Or.inr rfl
    · cases h_send with
      | send hST => exact absurd hST (fun h => PCRetrS_no_out h)
    · exact absurd rfl hne

theorem S16_step : ∀ (δ : net_label) (N' : Network),
    net_trans S16 δ N' → is_internal_net_label δ → N' = S10 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S16, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PCRetrS_inp_iff hST
        rcases hi with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · rw [qOK_OK] at hQ
          cases hQ
          rfl
        · rw [qOK_ERR] at hQ
          cases hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S16, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PCRetrS_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PSQRec_no_out h)
    · exact absurd rfl hne

theorem S17_step : ∀ (δ : net_label) (N' : Network),
    net_trans S17 δ N' → is_internal_net_label δ → N' = S10 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S17, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PCRetrS_inp_iff hST
        rcases hi with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · rw [qERR_OK] at hQ
          cases hQ
        · rw [qERR_ERR] at hQ
          cases hQ
          rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S17, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PCRetrS_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PSQRec_no_out h)
    · exact absurd rfl hne

theorem S18_step : ∀ (δ : net_label) (N' : Network),
    net_trans S18 δ N' → is_internal_net_label δ → N' = S19 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S18, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PSQRec_inp_iff hST
        rcases hi with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · rw [qDELE_LIST] at hQ
          cases hQ
        · rw [qDELE_RETR] at hQ
          cases hQ
        · rw [qDELE_DELE] at hQ
          cases hQ
          rfl
        · rw [qDELE_NOOP] at hQ
          cases hQ
        · rw [qDELE_QUIT] at hQ
          cases hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S18, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PSQRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PCDeleS_no_out h)
    · exact absurd rfl hne

theorem S19_step : ∀ (δ : net_label) (N' : Network),
    net_trans S19 δ N' → is_internal_net_label δ → N' = S20 ∨ N' = S21 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S19, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S19, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := PSDeleS_out_iff hST
          rcases ho with ⟨-, rfl, rfl, rfl⟩ | ⟨-, rfl, rfl, rfl⟩
          · exact Or.inl rfl
          · exact Or.inr rfl
    · cases h_send with
      | send hST => exact absurd hST (fun h => PCDeleS_no_out h)
    · exact absurd rfl hne

theorem S20_step : ∀ (δ : net_label) (N' : Network),
    net_trans S20 δ N' → is_internal_net_label δ → N' = S10 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S20, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PCDeleS_inp_iff hST
        rcases hi with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · rw [qOK_OK] at hQ
          cases hQ
          rfl
        · rw [qOK_ERR] at hQ
          cases hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S20, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PCDeleS_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PSQRec_no_out h)
    · exact absurd rfl hne

theorem S21_step : ∀ (δ : net_label) (N' : Network),
    net_trans S21 δ N' → is_internal_net_label δ → N' = S10 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S21, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PCDeleS_inp_iff hST
        rcases hi with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · rw [qERR_OK] at hQ
          cases hQ
        · rw [qERR_ERR] at hQ
          cases hQ
          rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S21, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PCDeleS_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PSQRec_no_out h)
    · exact absurd rfl hne


theorem S22_step : ∀ (δ : net_label) (N' : Network),
    net_trans S22 δ N' → is_internal_net_label δ → N' = S23 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S22, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PSQRec_inp_iff hST
        rcases hi with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · rw [qNOOP_LIST] at hQ
          cases hQ
        · rw [qNOOP_RETR] at hQ
          cases hQ
        · rw [qNOOP_DELE] at hQ
          cases hQ
        · rw [qNOOP_NOOP] at hQ
          cases hQ
          rfl
        · rw [qNOOP_QUIT] at hQ
          cases hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S22, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PSQRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PCNoopS_no_out h)
    · exact absurd rfl hne

theorem S23_step : ∀ (δ : net_label) (N' : Network),
    net_trans S23 δ N' → is_internal_net_label δ → N' = S24 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S23, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S23, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := PSNoopS_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          rfl
    · cases h_send with
      | send hST => exact absurd hST (fun h => PCNoopS_no_out h)
    · exact absurd rfl hne

theorem S24_step : ∀ (δ : net_label) (N' : Network),
    net_trans S24 δ N' → is_internal_net_label δ → N' = S10 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S24, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PCNoopS_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qOK_OK] at hQ
        cases hQ
        rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S24, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PCNoopS_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PSQRec_no_out h)
    · exact absurd rfl hne

theorem S25_step : ∀ (δ : net_label) (N' : Network),
    net_trans S25 δ N' → is_internal_net_label δ → N' = S26 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S25, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PSQRec_inp_iff hST
        rcases hi with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · rw [qQUIT_LIST] at hQ
          cases hQ
        · rw [qQUIT_RETR] at hQ
          cases hQ
        · rw [qQUIT_DELE] at hQ
          cases hQ
        · rw [qQUIT_NOOP] at hQ
          cases hQ
        · rw [qQUIT_QUIT] at hQ
          cases hQ
          rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S25, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PSQRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PCQuitS_no_out h)
    · exact absurd rfl hne

theorem S26_step : ∀ (δ : net_label) (N' : Network),
    net_trans S26 δ N' → is_internal_net_label δ → N' = S27 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S26, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S26, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := PSQuitS_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          rfl
    · cases h_send with
      | send hST => exact absurd hST (fun h => PCQuitS_no_out h)
    · exact absurd rfl hne

theorem S27_step : ∀ (δ : net_label) (N' : Network),
    net_trans S27 δ N' → is_internal_net_label δ → N' = S28 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S27, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PCQuitS_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        rw [qOK_OK] at hQ
        cases hQ
        rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S27, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PCQuitS_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · exact absurd rfl hne

theorem S28_no_step : ∀ (δ : net_label) (N' : Network),
    net_trans S28 δ N' → is_internal_net_label δ → False := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S28, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      (cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ)
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S28, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out h)
    · exact absurd rfl hne


-- Reachability: every τ-reachable network is one of the 29 states.
-- (Auxiliary with variable start so `induction` applies; instantiate at `Net`.)
theorem popReach_aux : ∀ (N1 N2 : Network), net_trans_star N1 N2 →
    (N1 = S0 ∨ N1 = S1 ∨ N1 = S2 ∨ N1 = S3 ∨ N1 = S4 ∨ N1 = S5 ∨ N1 = S6 ∨ N1 = S7 ∨ N1 = S8 ∨ N1 = S9 ∨ N1 = S10 ∨ N1 = S11 ∨ N1 = S12 ∨ N1 = S13 ∨ N1 = S14 ∨ N1 = S15 ∨ N1 = S16 ∨ N1 = S17 ∨ N1 = S18 ∨ N1 = S19 ∨ N1 = S20 ∨ N1 = S21 ∨ N1 = S22 ∨ N1 = S23 ∨ N1 = S24 ∨ N1 = S25 ∨ N1 = S26 ∨ N1 = S27 ∨ N1 = S28) →
    (N2 = S0 ∨ N2 = S1 ∨ N2 = S2 ∨ N2 = S3 ∨ N2 = S4 ∨ N2 = S5 ∨ N2 = S6 ∨ N2 = S7 ∨ N2 = S8 ∨ N2 = S9 ∨ N2 = S10 ∨ N2 = S11 ∨ N2 = S12 ∨ N2 = S13 ∨ N2 = S14 ∨ N2 = S15 ∨ N2 = S16 ∨ N2 = S17 ∨ N2 = S18 ∨ N2 = S19 ∨ N2 = S20 ∨ N2 = S21 ∨ N2 = S22 ∨ N2 = S23 ∨ N2 = S24 ∨ N2 = S25 ∨ N2 = S26 ∨ N2 = S27 ∨ N2 = S28) := by
  intro N1 N2 hStar
  induction hStar with
  | refl => intro h; exact h
  | step hInt hTr _ ih =>
    intro hN1
    rcases hN1 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h := S0_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S1_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S2_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S3_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S4_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S5_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S6_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S7_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S8_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S9_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S10_step _ _ hTr hInt
      rcases h with rfl | rfl | rfl | rfl | rfl
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S11_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S12_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S13_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S14_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S15_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S16_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S17_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S18_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S19_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
      · exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S20_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S21_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S22_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S23_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S24_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S25_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S26_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · have h := S27_step _ _ hTr hInt
      subst h
      exact ih (by repeat (first | exact Or.inl rfl | apply Or.inr); try rfl)
    · exact absurd (S28_no_step _ _ hTr hInt) id

theorem popReach : ∀ (N' : Network), net_trans_star Net N' →
    (N' = S0 ∨ N' = S1 ∨ N' = S2 ∨ N' = S3 ∨ N' = S4 ∨ N' = S5 ∨ N' = S6 ∨ N' = S7 ∨ N' = S8 ∨ N' = S9 ∨ N' = S10 ∨ N' = S11 ∨ N' = S12 ∨ N' = S13 ∨ N' = S14 ∨ N' = S15 ∨ N' = S16 ∨ N' = S17 ∨ N' = S18 ∨ N' = S19 ∨ N' = S20 ∨ N' = S21 ∨ N' = S22 ∨ N' = S23 ∨ N' = S24 ∨ N' = S25 ∨ N' = S26 ∨ N' = S27 ∨ N' = S28) :=
  fun N' hStar => popReach_aux Net N' hStar (Or.inl rfl)


-- ============ Explicit transitions (reused for stuck + output-live) ============
theorem t_S0_S1 : net_trans S0 (net_label.τ_comm "POPClient" "POPServer" "USER" "unit") S1 := by
  have h_send : sq_trans (POPClient, ([] : Queue))
      (sq_action.send "POPServer" "USER" "unit") (PCUserS, []) := by
    apply sq_trans.send
    unfold POPClient
    apply st_trans.tRec
    show st_trans PCSub _ _
    unfold PCSub
    apply st_trans.intC
    simp [PCUserS]
  have h_recv : sq_trans (POPServer, ([] : Queue))
      (sq_action.recv "POPClient" "USER" "unit") (POPServer, [mUSER]) :=
    sq_trans.recv
  have hmem_p : ("POPClient", (POPClient, ([] : Queue))) ∈ S0 := by simp [S0]
  have hmem_q : ("POPServer", (POPServer, ([] : Queue))) ∈ S0 := by simp [S0]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t_S1_S2 : net_trans S1 (net_label.τ_dequeue "POPServer" "POPClient" "USER" "unit") S2 := by
  have hSQ : sq_trans (POPServer, [mUSER])
      (sq_action.dequeue "POPClient" "USER" "unit") (PSUserS, []) := by
    apply sq_trans.dequeue
    · unfold POPServer
      apply st_trans.tRec
      show st_trans PSSub _ _
      unfold PSSub
      apply st_trans.extC
      simp [PSUserS]
    · exact qUSER_USER
  have hmem : ("POPServer", (POPServer, [mUSER])) ∈ S1 := by simp [S1]
  exact net_trans.dequeue hSQ hmem

theorem t_S2_S3 : net_trans S2 (net_label.τ_comm "POPServer" "POPClient" "ERR" "unit") S3 := by
  have h_send : sq_trans (PSUserS, ([] : Queue))
      (sq_action.send "POPClient" "ERR" "unit") (PSRec, []) := by
    apply sq_trans.send
    unfold PSUserS
    apply st_trans.intC
    simp [PSRec]
  have h_recv : sq_trans (PCUserS, ([] : Queue))
      (sq_action.recv "POPServer" "ERR" "unit") (PCUserS, [mERR]) :=
    sq_trans.recv
  have hmem_p : ("POPServer", (PSUserS, ([] : Queue))) ∈ S2 := by simp [S2]
  have hmem_q : ("POPClient", (PCUserS, ([] : Queue))) ∈ S2 := by simp [S2]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t_S2_S4 : net_trans S2 (net_label.τ_comm "POPServer" "POPClient" "OK" "unit") S4 := by
  have h_send : sq_trans (PSUserS, ([] : Queue))
      (sq_action.send "POPClient" "OK" "unit") (PSSpassS, []) := by
    apply sq_trans.send
    unfold PSUserS
    apply st_trans.intC
    simp [PSSpassS]
  have h_recv : sq_trans (PCUserS, ([] : Queue))
      (sq_action.recv "POPServer" "OK" "unit") (PCUserS, [mOK]) :=
    sq_trans.recv
  have hmem_p : ("POPServer", (PSUserS, ([] : Queue))) ∈ S2 := by simp [S2]
  have hmem_q : ("POPClient", (PCUserS, ([] : Queue))) ∈ S2 := by simp [S2]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t_S3_S0 : net_trans S3 (net_label.τ_dequeue "POPClient" "POPServer" "ERR" "unit") S0 := by
  have hSQ : sq_trans (PCUserS, [mERR])
      (sq_action.dequeue "POPServer" "ERR" "unit") (PCRec, []) := by
    apply sq_trans.dequeue
    · unfold PCUserS
      apply st_trans.extC
      simp [PCRec]
    · exact qERR_ERR
  have hmem : ("POPClient", (PCUserS, [mERR])) ∈ S3 := by simp [S3]
  exact net_trans.dequeue hSQ hmem

theorem t_S4_S5 : net_trans S4 (net_label.τ_dequeue "POPClient" "POPServer" "OK" "unit") S5 := by
  have hSQ : sq_trans (PCUserS, [mOK])
      (sq_action.dequeue "POPServer" "OK" "unit") (PCPassS, []) := by
    apply sq_trans.dequeue
    · unfold PCUserS
      apply st_trans.extC
      simp [PCPassS]
    · exact qOK_OK
  have hmem : ("POPClient", (PCUserS, [mOK])) ∈ S4 := by simp [S4]
  exact net_trans.dequeue hSQ hmem

theorem t_S5_S6 : net_trans S5 (net_label.τ_comm "POPClient" "POPServer" "PASS" "unit") S6 := by
  have h_send : sq_trans (PCPassS, ([] : Queue))
      (sq_action.send "POPServer" "PASS" "unit") (PCPassES, []) := by
    apply sq_trans.send
    unfold PCPassS
    apply st_trans.intC
    simp [PCPassES]
  have h_recv : sq_trans (PSSpassS, ([] : Queue))
      (sq_action.recv "POPClient" "PASS" "unit") (PSSpassS, [mPASS]) :=
    sq_trans.recv
  have hmem_p : ("POPClient", (PCPassS, ([] : Queue))) ∈ S5 := by simp [S5]
  have hmem_q : ("POPServer", (PSSpassS, ([] : Queue))) ∈ S5 := by simp [S5]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t_S6_S7 : net_trans S6 (net_label.τ_dequeue "POPServer" "POPClient" "PASS" "unit") S7 := by
  have hSQ : sq_trans (PSSpassS, [mPASS])
      (sq_action.dequeue "POPClient" "PASS" "unit") (PSSpeS, []) := by
    apply sq_trans.dequeue
    · unfold PSSpassS
      apply st_trans.extC
      simp [PSSpeS]
    · exact qPASS_PASS
  have hmem : ("POPServer", (PSSpassS, [mPASS])) ∈ S6 := by simp [S6]
  exact net_trans.dequeue hSQ hmem

theorem t_S7_S8 : net_trans S7 (net_label.τ_comm "POPServer" "POPClient" "ERR" "unit") S8 := by
  have h_send : sq_trans (PSSpeS, ([] : Queue))
      (sq_action.send "POPClient" "ERR" "unit") (PSRec, []) := by
    apply sq_trans.send
    unfold PSSpeS
    apply st_trans.intC
    simp [PSRec]
  have h_recv : sq_trans (PCPassES, ([] : Queue))
      (sq_action.recv "POPServer" "ERR" "unit") (PCPassES, [mERR]) :=
    sq_trans.recv
  have hmem_p : ("POPServer", (PSSpeS, ([] : Queue))) ∈ S7 := by simp [S7]
  have hmem_q : ("POPClient", (PCPassES, ([] : Queue))) ∈ S7 := by simp [S7]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t_S7_S9 : net_trans S7 (net_label.τ_comm "POPServer" "POPClient" "OK" "unit") S9 := by
  have h_send : sq_trans (PSSpeS, ([] : Queue))
      (sq_action.send "POPClient" "OK" "unit") (PSQRec, []) := by
    apply sq_trans.send
    unfold PSSpeS
    apply st_trans.intC
    simp [PSQRec]
  have h_recv : sq_trans (PCPassES, ([] : Queue))
      (sq_action.recv "POPServer" "OK" "unit") (PCPassES, [mOK]) :=
    sq_trans.recv
  have hmem_p : ("POPServer", (PSSpeS, ([] : Queue))) ∈ S7 := by simp [S7]
  have hmem_q : ("POPClient", (PCPassES, ([] : Queue))) ∈ S7 := by simp [S7]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t_S8_S0 : net_trans S8 (net_label.τ_dequeue "POPClient" "POPServer" "ERR" "unit") S0 := by
  have hSQ : sq_trans (PCPassES, [mERR])
      (sq_action.dequeue "POPServer" "ERR" "unit") (PCRec, []) := by
    apply sq_trans.dequeue
    · unfold PCPassES
      apply st_trans.extC
      simp [PCRec]
    · exact qERR_ERR
  have hmem : ("POPClient", (PCPassES, [mERR])) ∈ S8 := by simp [S8]
  exact net_trans.dequeue hSQ hmem

theorem t_S9_S10 : net_trans S9 (net_label.τ_dequeue "POPClient" "POPServer" "OK" "unit") S10 := by
  have hSQ : sq_trans (PCPassES, [mOK])
      (sq_action.dequeue "POPServer" "OK" "unit") (PCQRec, []) := by
    apply sq_trans.dequeue
    · unfold PCPassES
      apply st_trans.extC
      simp [PCQRec]
    · exact qOK_OK
  have hmem : ("POPClient", (PCPassES, [mOK])) ∈ S9 := by simp [S9]
  exact net_trans.dequeue hSQ hmem

theorem t_S10_S11 : net_trans S10 (net_label.τ_comm "POPClient" "POPServer" "LIST" "unit") S11 := by
  have h_send : sq_trans (PCQRec, ([] : Queue))
      (sq_action.send "POPServer" "LIST" "unit") (PCListS, []) := by
    apply sq_trans.send
    unfold PCQRec
    apply st_trans.tRec
    show st_trans PCQSub _ _
    unfold PCQSub
    apply st_trans.intC
    simp [PCListS]
  have h_recv : sq_trans (PSQRec, ([] : Queue))
      (sq_action.recv "POPClient" "LIST" "unit") (PSQRec, [mLIST]) :=
    sq_trans.recv
  have hmem_p : ("POPClient", (PCQRec, ([] : Queue))) ∈ S10 := by simp [S10]
  have hmem_q : ("POPServer", (PSQRec, ([] : Queue))) ∈ S10 := by simp [S10]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t_S10_S14 : net_trans S10 (net_label.τ_comm "POPClient" "POPServer" "RETR" "unit") S14 := by
  have h_send : sq_trans (PCQRec, ([] : Queue))
      (sq_action.send "POPServer" "RETR" "unit") (PCRetrS, []) := by
    apply sq_trans.send
    unfold PCQRec
    apply st_trans.tRec
    show st_trans PCQSub _ _
    unfold PCQSub
    apply st_trans.intC
    simp [PCRetrS]
  have h_recv : sq_trans (PSQRec, ([] : Queue))
      (sq_action.recv "POPClient" "RETR" "unit") (PSQRec, [mRETR]) :=
    sq_trans.recv
  have hmem_p : ("POPClient", (PCQRec, ([] : Queue))) ∈ S10 := by simp [S10]
  have hmem_q : ("POPServer", (PSQRec, ([] : Queue))) ∈ S10 := by simp [S10]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t_S10_S18 : net_trans S10 (net_label.τ_comm "POPClient" "POPServer" "DELE" "unit") S18 := by
  have h_send : sq_trans (PCQRec, ([] : Queue))
      (sq_action.send "POPServer" "DELE" "unit") (PCDeleS, []) := by
    apply sq_trans.send
    unfold PCQRec
    apply st_trans.tRec
    show st_trans PCQSub _ _
    unfold PCQSub
    apply st_trans.intC
    simp [PCDeleS]
  have h_recv : sq_trans (PSQRec, ([] : Queue))
      (sq_action.recv "POPClient" "DELE" "unit") (PSQRec, [mDELE]) :=
    sq_trans.recv
  have hmem_p : ("POPClient", (PCQRec, ([] : Queue))) ∈ S10 := by simp [S10]
  have hmem_q : ("POPServer", (PSQRec, ([] : Queue))) ∈ S10 := by simp [S10]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t_S10_S22 : net_trans S10 (net_label.τ_comm "POPClient" "POPServer" "NOOP" "unit") S22 := by
  have h_send : sq_trans (PCQRec, ([] : Queue))
      (sq_action.send "POPServer" "NOOP" "unit") (PCNoopS, []) := by
    apply sq_trans.send
    unfold PCQRec
    apply st_trans.tRec
    show st_trans PCQSub _ _
    unfold PCQSub
    apply st_trans.intC
    simp [PCNoopS]
  have h_recv : sq_trans (PSQRec, ([] : Queue))
      (sq_action.recv "POPClient" "NOOP" "unit") (PSQRec, [mNOOP]) :=
    sq_trans.recv
  have hmem_p : ("POPClient", (PCQRec, ([] : Queue))) ∈ S10 := by simp [S10]
  have hmem_q : ("POPServer", (PSQRec, ([] : Queue))) ∈ S10 := by simp [S10]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t_S10_S25 : net_trans S10 (net_label.τ_comm "POPClient" "POPServer" "QUIT" "unit") S25 := by
  have h_send : sq_trans (PCQRec, ([] : Queue))
      (sq_action.send "POPServer" "QUIT" "unit") (PCQuitS, []) := by
    apply sq_trans.send
    unfold PCQRec
    apply st_trans.tRec
    show st_trans PCQSub _ _
    unfold PCQSub
    apply st_trans.intC
    simp [PCQuitS]
  have h_recv : sq_trans (PSQRec, ([] : Queue))
      (sq_action.recv "POPClient" "QUIT" "unit") (PSQRec, [mQUIT]) :=
    sq_trans.recv
  have hmem_p : ("POPClient", (PCQRec, ([] : Queue))) ∈ S10 := by simp [S10]
  have hmem_q : ("POPServer", (PSQRec, ([] : Queue))) ∈ S10 := by simp [S10]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t_S11_S12 : net_trans S11 (net_label.τ_dequeue "POPServer" "POPClient" "LIST" "unit") S12 := by
  have hSQ : sq_trans (PSQRec, [mLIST])
      (sq_action.dequeue "POPClient" "LIST" "unit") (PSListS, []) := by
    apply sq_trans.dequeue
    · unfold PSQRec
      apply st_trans.tRec
      show st_trans PSQSub _ _
      unfold PSQSub
      apply st_trans.extC
      simp [PSListS]
    · exact qLIST_LIST
  have hmem : ("POPServer", (PSQRec, [mLIST])) ∈ S11 := by simp [S11]
  exact net_trans.dequeue hSQ hmem

theorem t_S12_S13 : net_trans S12 (net_label.τ_comm "POPServer" "POPClient" "MSGS" "unit") S13 := by
  have h_send : sq_trans (PSListS, ([] : Queue))
      (sq_action.send "POPClient" "MSGS" "unit") (PSQRec, []) := by
    apply sq_trans.send
    unfold PSListS
    apply st_trans.intC
    simp [PSQRec]
  have h_recv : sq_trans (PCListS, ([] : Queue))
      (sq_action.recv "POPServer" "MSGS" "unit") (PCListS, [mMSGS]) :=
    sq_trans.recv
  have hmem_p : ("POPServer", (PSListS, ([] : Queue))) ∈ S12 := by simp [S12]
  have hmem_q : ("POPClient", (PCListS, ([] : Queue))) ∈ S12 := by simp [S12]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t_S13_S10 : net_trans S13 (net_label.τ_dequeue "POPClient" "POPServer" "MSGS" "unit") S10 := by
  have hSQ : sq_trans (PCListS, [mMSGS])
      (sq_action.dequeue "POPServer" "MSGS" "unit") (PCQRec, []) := by
    apply sq_trans.dequeue
    · unfold PCListS
      apply st_trans.extC
      simp [PCQRec]
    · exact qMSGS_MSGS
  have hmem : ("POPClient", (PCListS, [mMSGS])) ∈ S13 := by simp [S13]
  exact net_trans.dequeue hSQ hmem

theorem t_S14_S15 : net_trans S14 (net_label.τ_dequeue "POPServer" "POPClient" "RETR" "unit") S15 := by
  have hSQ : sq_trans (PSQRec, [mRETR])
      (sq_action.dequeue "POPClient" "RETR" "unit") (PSRetrS, []) := by
    apply sq_trans.dequeue
    · unfold PSQRec
      apply st_trans.tRec
      show st_trans PSQSub _ _
      unfold PSQSub
      apply st_trans.extC
      simp [PSRetrS]
    · exact qRETR_RETR
  have hmem : ("POPServer", (PSQRec, [mRETR])) ∈ S14 := by simp [S14]
  exact net_trans.dequeue hSQ hmem

theorem t_S15_S16 : net_trans S15 (net_label.τ_comm "POPServer" "POPClient" "OK" "unit") S16 := by
  have h_send : sq_trans (PSRetrS, ([] : Queue))
      (sq_action.send "POPClient" "OK" "unit") (PSQRec, []) := by
    apply sq_trans.send
    unfold PSRetrS
    apply st_trans.intC
    simp [PSQRec]
  have h_recv : sq_trans (PCRetrS, ([] : Queue))
      (sq_action.recv "POPServer" "OK" "unit") (PCRetrS, [mOK]) :=
    sq_trans.recv
  have hmem_p : ("POPServer", (PSRetrS, ([] : Queue))) ∈ S15 := by simp [S15]
  have hmem_q : ("POPClient", (PCRetrS, ([] : Queue))) ∈ S15 := by simp [S15]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t_S15_S17 : net_trans S15 (net_label.τ_comm "POPServer" "POPClient" "ERR" "unit") S17 := by
  have h_send : sq_trans (PSRetrS, ([] : Queue))
      (sq_action.send "POPClient" "ERR" "unit") (PSQRec, []) := by
    apply sq_trans.send
    unfold PSRetrS
    apply st_trans.intC
    simp [PSQRec]
  have h_recv : sq_trans (PCRetrS, ([] : Queue))
      (sq_action.recv "POPServer" "ERR" "unit") (PCRetrS, [mERR]) :=
    sq_trans.recv
  have hmem_p : ("POPServer", (PSRetrS, ([] : Queue))) ∈ S15 := by simp [S15]
  have hmem_q : ("POPClient", (PCRetrS, ([] : Queue))) ∈ S15 := by simp [S15]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t_S16_S10 : net_trans S16 (net_label.τ_dequeue "POPClient" "POPServer" "OK" "unit") S10 := by
  have hSQ : sq_trans (PCRetrS, [mOK])
      (sq_action.dequeue "POPServer" "OK" "unit") (PCQRec, []) := by
    apply sq_trans.dequeue
    · unfold PCRetrS
      apply st_trans.extC
      simp [PCQRec]
    · exact qOK_OK
  have hmem : ("POPClient", (PCRetrS, [mOK])) ∈ S16 := by simp [S16]
  exact net_trans.dequeue hSQ hmem

theorem t_S17_S10 : net_trans S17 (net_label.τ_dequeue "POPClient" "POPServer" "ERR" "unit") S10 := by
  have hSQ : sq_trans (PCRetrS, [mERR])
      (sq_action.dequeue "POPServer" "ERR" "unit") (PCQRec, []) := by
    apply sq_trans.dequeue
    · unfold PCRetrS
      apply st_trans.extC
      simp [PCQRec]
    · exact qERR_ERR
  have hmem : ("POPClient", (PCRetrS, [mERR])) ∈ S17 := by simp [S17]
  exact net_trans.dequeue hSQ hmem

theorem t_S18_S19 : net_trans S18 (net_label.τ_dequeue "POPServer" "POPClient" "DELE" "unit") S19 := by
  have hSQ : sq_trans (PSQRec, [mDELE])
      (sq_action.dequeue "POPClient" "DELE" "unit") (PSDeleS, []) := by
    apply sq_trans.dequeue
    · unfold PSQRec
      apply st_trans.tRec
      show st_trans PSQSub _ _
      unfold PSQSub
      apply st_trans.extC
      simp [PSDeleS]
    · exact qDELE_DELE
  have hmem : ("POPServer", (PSQRec, [mDELE])) ∈ S18 := by simp [S18]
  exact net_trans.dequeue hSQ hmem

theorem t_S19_S20 : net_trans S19 (net_label.τ_comm "POPServer" "POPClient" "OK" "unit") S20 := by
  have h_send : sq_trans (PSDeleS, ([] : Queue))
      (sq_action.send "POPClient" "OK" "unit") (PSQRec, []) := by
    apply sq_trans.send
    unfold PSDeleS
    apply st_trans.intC
    simp [PSQRec]
  have h_recv : sq_trans (PCDeleS, ([] : Queue))
      (sq_action.recv "POPServer" "OK" "unit") (PCDeleS, [mOK]) :=
    sq_trans.recv
  have hmem_p : ("POPServer", (PSDeleS, ([] : Queue))) ∈ S19 := by simp [S19]
  have hmem_q : ("POPClient", (PCDeleS, ([] : Queue))) ∈ S19 := by simp [S19]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t_S19_S21 : net_trans S19 (net_label.τ_comm "POPServer" "POPClient" "ERR" "unit") S21 := by
  have h_send : sq_trans (PSDeleS, ([] : Queue))
      (sq_action.send "POPClient" "ERR" "unit") (PSQRec, []) := by
    apply sq_trans.send
    unfold PSDeleS
    apply st_trans.intC
    simp [PSQRec]
  have h_recv : sq_trans (PCDeleS, ([] : Queue))
      (sq_action.recv "POPServer" "ERR" "unit") (PCDeleS, [mERR]) :=
    sq_trans.recv
  have hmem_p : ("POPServer", (PSDeleS, ([] : Queue))) ∈ S19 := by simp [S19]
  have hmem_q : ("POPClient", (PCDeleS, ([] : Queue))) ∈ S19 := by simp [S19]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t_S20_S10 : net_trans S20 (net_label.τ_dequeue "POPClient" "POPServer" "OK" "unit") S10 := by
  have hSQ : sq_trans (PCDeleS, [mOK])
      (sq_action.dequeue "POPServer" "OK" "unit") (PCQRec, []) := by
    apply sq_trans.dequeue
    · unfold PCDeleS
      apply st_trans.extC
      simp [PCQRec]
    · exact qOK_OK
  have hmem : ("POPClient", (PCDeleS, [mOK])) ∈ S20 := by simp [S20]
  exact net_trans.dequeue hSQ hmem

theorem t_S21_S10 : net_trans S21 (net_label.τ_dequeue "POPClient" "POPServer" "ERR" "unit") S10 := by
  have hSQ : sq_trans (PCDeleS, [mERR])
      (sq_action.dequeue "POPServer" "ERR" "unit") (PCQRec, []) := by
    apply sq_trans.dequeue
    · unfold PCDeleS
      apply st_trans.extC
      simp [PCQRec]
    · exact qERR_ERR
  have hmem : ("POPClient", (PCDeleS, [mERR])) ∈ S21 := by simp [S21]
  exact net_trans.dequeue hSQ hmem

theorem t_S22_S23 : net_trans S22 (net_label.τ_dequeue "POPServer" "POPClient" "NOOP" "unit") S23 := by
  have hSQ : sq_trans (PSQRec, [mNOOP])
      (sq_action.dequeue "POPClient" "NOOP" "unit") (PSNoopS, []) := by
    apply sq_trans.dequeue
    · unfold PSQRec
      apply st_trans.tRec
      show st_trans PSQSub _ _
      unfold PSQSub
      apply st_trans.extC
      simp [PSNoopS]
    · exact qNOOP_NOOP
  have hmem : ("POPServer", (PSQRec, [mNOOP])) ∈ S22 := by simp [S22]
  exact net_trans.dequeue hSQ hmem

theorem t_S23_S24 : net_trans S23 (net_label.τ_comm "POPServer" "POPClient" "OK" "unit") S24 := by
  have h_send : sq_trans (PSNoopS, ([] : Queue))
      (sq_action.send "POPClient" "OK" "unit") (PSQRec, []) := by
    apply sq_trans.send
    unfold PSNoopS
    apply st_trans.intC
    simp [PSQRec]
  have h_recv : sq_trans (PCNoopS, ([] : Queue))
      (sq_action.recv "POPServer" "OK" "unit") (PCNoopS, [mOK]) :=
    sq_trans.recv
  have hmem_p : ("POPServer", (PSNoopS, ([] : Queue))) ∈ S23 := by simp [S23]
  have hmem_q : ("POPClient", (PCNoopS, ([] : Queue))) ∈ S23 := by simp [S23]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t_S24_S10 : net_trans S24 (net_label.τ_dequeue "POPClient" "POPServer" "OK" "unit") S10 := by
  have hSQ : sq_trans (PCNoopS, [mOK])
      (sq_action.dequeue "POPServer" "OK" "unit") (PCQRec, []) := by
    apply sq_trans.dequeue
    · unfold PCNoopS
      apply st_trans.extC
      simp [PCQRec]
    · exact qOK_OK
  have hmem : ("POPClient", (PCNoopS, [mOK])) ∈ S24 := by simp [S24]
  exact net_trans.dequeue hSQ hmem

theorem t_S25_S26 : net_trans S25 (net_label.τ_dequeue "POPServer" "POPClient" "QUIT" "unit") S26 := by
  have hSQ : sq_trans (PSQRec, [mQUIT])
      (sq_action.dequeue "POPClient" "QUIT" "unit") (PSQuitS, []) := by
    apply sq_trans.dequeue
    · unfold PSQRec
      apply st_trans.tRec
      show st_trans PSQSub _ _
      unfold PSQSub
      apply st_trans.extC
      simp [PSQuitS]
    · exact qQUIT_QUIT
  have hmem : ("POPServer", (PSQRec, [mQUIT])) ∈ S25 := by simp [S25]
  exact net_trans.dequeue hSQ hmem

theorem t_S26_S27 : net_trans S26 (net_label.τ_comm "POPServer" "POPClient" "OK" "unit") S27 := by
  have h_send : sq_trans (PSQuitS, ([] : Queue))
      (sq_action.send "POPClient" "OK" "unit") (SessionType.tEnd, []) := by
    apply sq_trans.send
    unfold PSQuitS
    apply st_trans.intC
    simp
  have h_recv : sq_trans (PCQuitS, ([] : Queue))
      (sq_action.recv "POPServer" "OK" "unit") (PCQuitS, [mOK]) :=
    sq_trans.recv
  have hmem_p : ("POPServer", (PSQuitS, ([] : Queue))) ∈ S26 := by simp [S26]
  have hmem_q : ("POPClient", (PCQuitS, ([] : Queue))) ∈ S26 := by simp [S26]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q

theorem t_S27_S28 : net_trans S27 (net_label.τ_dequeue "POPClient" "POPServer" "OK" "unit") S28 := by
  have hSQ : sq_trans (PCQuitS, [mOK])
      (sq_action.dequeue "POPServer" "OK" "unit") (SessionType.tEnd, []) := by
    apply sq_trans.dequeue
    · unfold PCQuitS
      apply st_trans.extC
      simp
    · exact qOK_OK
  have hmem : ("POPClient", (PCQuitS, [mOK])) ∈ S27 := by simp [S27]
  exact net_trans.dequeue hSQ hmem


/-- `Net` is half-duplex: opposite queues never both fill. -/
theorem Net_halfDuplex : IsHalfDuplex Net := by
  intro N' hStar p q Qp Qq hP hQ hCp hCq
  have hR := popReach N' hStar
  rcases hR with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- S0: both queues empty
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S0, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      exact absurd hCp noContainsNil
  · -- S1: S holds [USER]
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
  · -- S3: C holds [ERR]
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
  · -- S4: C holds [OK]
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S4, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S5: both empty
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S5, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      exact absurd hCp noContainsNil
  · -- S6: S holds [PASS]
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S6, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S7: both empty
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S7, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      exact absurd hCp noContainsNil
  · -- S8: C holds [ERR]
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S8, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S9: C holds [OK]
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
  · -- S10: both empty
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S10, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      exact absurd hCp noContainsNil
  · -- S11: S holds [LIST]
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
  · -- S13: C holds [MSGS]
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S13, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S14: S holds [RETR]
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S14, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S15: both empty
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S15, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      exact absurd hCp noContainsNil
  · -- S16: C holds [OK]
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S16, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S17: C holds [ERR]
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S17, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S18: S holds [DELE]
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S18, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S19: both empty
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S19, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      exact absurd hCp noContainsNil
  · -- S20: C holds [OK]
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S20, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S21: C holds [ERR]
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S21, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S22: S holds [NOOP]
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S22, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S23: both empty
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S23, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      exact absurd hCp noContainsNil
  · -- S24: C holds [OK]
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S24, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S25: S holds [QUIT]
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S25, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S26: both empty
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S26, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      exact absurd hCp noContainsNil
  · -- S27: C holds [OK], S ended
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S27, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S28: both empty
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S28, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      exact absurd hCp noContainsNil


-- ============ Output-liveness: infinite fair paths ============
/-- Every infinite fair path from `Net` is output-live. -/
theorem popOL_inf : IsOutputLiveInfinitePathNetwork Net := by
  intro path h0 hfair i p Qp hmemP q lab S hdeq
  have hStar : net_trans_star Net (path.seq i) := path_star_reachable h0 i
  have hR := popReach _ hStar
  rcases hR with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · -- S0: queues empty, hdeq impossible
    rw [h] at hmemP
    obtain ⟨T, hP⟩ := hmemP
    simp only [S0, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      (obtain ⟨Q', hQ⟩ := hdeq; simp [Queue.dequeue, Queue.dequeue.go] at hQ)
  · -- S1: S holds [USER]
    rw [h] at hmemP
    obtain ⟨T, hP⟩ := hmemP
    simp only [S1, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mUSER] := Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      have hq : q = "POPClient" := congrArg (fun m => m.1) hmem
      have hlab : lab = "USER" := congrArg (fun m => m.2) hmem
      have hS : S = "unit" := congrArg (fun m => m.3) hmem
      subst hq; subst hlab; subst hS
      exact (hfair i).2 "POPServer" "POPClient" "USER" "unit"
        ⟨S2, by rw [h]; exact t_S1_S2⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- S2: queues empty
    rw [h] at hmemP
    obtain ⟨T, hP⟩ := hmemP
    simp only [S2, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      (obtain ⟨Q', hQ⟩ := hdeq; simp [Queue.dequeue, Queue.dequeue.go] at hQ)
  · -- S3: C holds [ERR]
    rw [h] at hmemP
    obtain ⟨T, hP⟩ := hmemP
    simp only [S3, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mERR] := Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      have hq : q = "POPServer" := congrArg (fun m => m.1) hmem
      have hlab : lab = "ERR" := congrArg (fun m => m.2) hmem
      have hS : S = "unit" := congrArg (fun m => m.3) hmem
      subst hq; subst hlab; subst hS
      exact (hfair i).2 "POPClient" "POPServer" "ERR" "unit"
        ⟨S0, by rw [h]; exact t_S3_S0⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- S4: C holds [OK]
    rw [h] at hmemP
    obtain ⟨T, hP⟩ := hmemP
    simp only [S4, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mOK] := Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      have hq : q = "POPServer" := congrArg (fun m => m.1) hmem
      have hlab : lab = "OK" := congrArg (fun m => m.2) hmem
      have hS : S = "unit" := congrArg (fun m => m.3) hmem
      subst hq; subst hlab; subst hS
      exact (hfair i).2 "POPClient" "POPServer" "OK" "unit"
        ⟨S5, by rw [h]; exact t_S4_S5⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- S5: queues empty
    rw [h] at hmemP
    obtain ⟨T, hP⟩ := hmemP
    simp only [S5, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      (obtain ⟨Q', hQ⟩ := hdeq; simp [Queue.dequeue, Queue.dequeue.go] at hQ)
  · -- S6: S holds [PASS]
    rw [h] at hmemP
    obtain ⟨T, hP⟩ := hmemP
    simp only [S6, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mPASS] := Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      have hq : q = "POPClient" := congrArg (fun m => m.1) hmem
      have hlab : lab = "PASS" := congrArg (fun m => m.2) hmem
      have hS : S = "unit" := congrArg (fun m => m.3) hmem
      subst hq; subst hlab; subst hS
      exact (hfair i).2 "POPServer" "POPClient" "PASS" "unit"
        ⟨S7, by rw [h]; exact t_S6_S7⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- S7: queues empty
    rw [h] at hmemP
    obtain ⟨T, hP⟩ := hmemP
    simp only [S7, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      (obtain ⟨Q', hQ⟩ := hdeq; simp [Queue.dequeue, Queue.dequeue.go] at hQ)
  · -- S8: C holds [ERR]
    rw [h] at hmemP
    obtain ⟨T, hP⟩ := hmemP
    simp only [S8, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mERR] := Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      have hq : q = "POPServer" := congrArg (fun m => m.1) hmem
      have hlab : lab = "ERR" := congrArg (fun m => m.2) hmem
      have hS : S = "unit" := congrArg (fun m => m.3) hmem
      subst hq; subst hlab; subst hS
      exact (hfair i).2 "POPClient" "POPServer" "ERR" "unit"
        ⟨S0, by rw [h]; exact t_S8_S0⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- S9: C holds [OK]
    rw [h] at hmemP
    obtain ⟨T, hP⟩ := hmemP
    simp only [S9, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mOK] := Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      have hq : q = "POPServer" := congrArg (fun m => m.1) hmem
      have hlab : lab = "OK" := congrArg (fun m => m.2) hmem
      have hS : S = "unit" := congrArg (fun m => m.3) hmem
      subst hq; subst hlab; subst hS
      exact (hfair i).2 "POPClient" "POPServer" "OK" "unit"
        ⟨S10, by rw [h]; exact t_S9_S10⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- S10: queues empty
    rw [h] at hmemP
    obtain ⟨T, hP⟩ := hmemP
    simp only [S10, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      (obtain ⟨Q', hQ⟩ := hdeq; simp [Queue.dequeue, Queue.dequeue.go] at hQ)
  · -- S11: S holds [LIST]
    rw [h] at hmemP
    obtain ⟨T, hP⟩ := hmemP
    simp only [S11, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mLIST] := Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      have hq : q = "POPClient" := congrArg (fun m => m.1) hmem
      have hlab : lab = "LIST" := congrArg (fun m => m.2) hmem
      have hS : S = "unit" := congrArg (fun m => m.3) hmem
      subst hq; subst hlab; subst hS
      exact (hfair i).2 "POPServer" "POPClient" "LIST" "unit"
        ⟨S12, by rw [h]; exact t_S11_S12⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- S12: queues empty
    rw [h] at hmemP
    obtain ⟨T, hP⟩ := hmemP
    simp only [S12, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      (obtain ⟨Q', hQ⟩ := hdeq; simp [Queue.dequeue, Queue.dequeue.go] at hQ)
  · -- S13: C holds [MSGS]
    rw [h] at hmemP
    obtain ⟨T, hP⟩ := hmemP
    simp only [S13, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mMSGS] := Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      have hq : q = "POPServer" := congrArg (fun m => m.1) hmem
      have hlab : lab = "MSGS" := congrArg (fun m => m.2) hmem
      have hS : S = "unit" := congrArg (fun m => m.3) hmem
      subst hq; subst hlab; subst hS
      exact (hfair i).2 "POPClient" "POPServer" "MSGS" "unit"
        ⟨S10, by rw [h]; exact t_S13_S10⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- S14: S holds [RETR]
    rw [h] at hmemP
    obtain ⟨T, hP⟩ := hmemP
    simp only [S14, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mRETR] := Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      have hq : q = "POPClient" := congrArg (fun m => m.1) hmem
      have hlab : lab = "RETR" := congrArg (fun m => m.2) hmem
      have hS : S = "unit" := congrArg (fun m => m.3) hmem
      subst hq; subst hlab; subst hS
      exact (hfair i).2 "POPServer" "POPClient" "RETR" "unit"
        ⟨S15, by rw [h]; exact t_S14_S15⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- S15: queues empty
    rw [h] at hmemP
    obtain ⟨T, hP⟩ := hmemP
    simp only [S15, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      (obtain ⟨Q', hQ⟩ := hdeq; simp [Queue.dequeue, Queue.dequeue.go] at hQ)
  · -- S16: C holds [OK]
    rw [h] at hmemP
    obtain ⟨T, hP⟩ := hmemP
    simp only [S16, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mOK] := Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      have hq : q = "POPServer" := congrArg (fun m => m.1) hmem
      have hlab : lab = "OK" := congrArg (fun m => m.2) hmem
      have hS : S = "unit" := congrArg (fun m => m.3) hmem
      subst hq; subst hlab; subst hS
      exact (hfair i).2 "POPClient" "POPServer" "OK" "unit"
        ⟨S10, by rw [h]; exact t_S16_S10⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- S17: C holds [ERR]
    rw [h] at hmemP
    obtain ⟨T, hP⟩ := hmemP
    simp only [S17, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mERR] := Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      have hq : q = "POPServer" := congrArg (fun m => m.1) hmem
      have hlab : lab = "ERR" := congrArg (fun m => m.2) hmem
      have hS : S = "unit" := congrArg (fun m => m.3) hmem
      subst hq; subst hlab; subst hS
      exact (hfair i).2 "POPClient" "POPServer" "ERR" "unit"
        ⟨S10, by rw [h]; exact t_S17_S10⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- S18: S holds [DELE]
    rw [h] at hmemP
    obtain ⟨T, hP⟩ := hmemP
    simp only [S18, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mDELE] := Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      have hq : q = "POPClient" := congrArg (fun m => m.1) hmem
      have hlab : lab = "DELE" := congrArg (fun m => m.2) hmem
      have hS : S = "unit" := congrArg (fun m => m.3) hmem
      subst hq; subst hlab; subst hS
      exact (hfair i).2 "POPServer" "POPClient" "DELE" "unit"
        ⟨S19, by rw [h]; exact t_S18_S19⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- S19: queues empty
    rw [h] at hmemP
    obtain ⟨T, hP⟩ := hmemP
    simp only [S19, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      (obtain ⟨Q', hQ⟩ := hdeq; simp [Queue.dequeue, Queue.dequeue.go] at hQ)
  · -- S20: C holds [OK]
    rw [h] at hmemP
    obtain ⟨T, hP⟩ := hmemP
    simp only [S20, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mOK] := Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      have hq : q = "POPServer" := congrArg (fun m => m.1) hmem
      have hlab : lab = "OK" := congrArg (fun m => m.2) hmem
      have hS : S = "unit" := congrArg (fun m => m.3) hmem
      subst hq; subst hlab; subst hS
      exact (hfair i).2 "POPClient" "POPServer" "OK" "unit"
        ⟨S10, by rw [h]; exact t_S20_S10⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- S21: C holds [ERR]
    rw [h] at hmemP
    obtain ⟨T, hP⟩ := hmemP
    simp only [S21, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mERR] := Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      have hq : q = "POPServer" := congrArg (fun m => m.1) hmem
      have hlab : lab = "ERR" := congrArg (fun m => m.2) hmem
      have hS : S = "unit" := congrArg (fun m => m.3) hmem
      subst hq; subst hlab; subst hS
      exact (hfair i).2 "POPClient" "POPServer" "ERR" "unit"
        ⟨S10, by rw [h]; exact t_S21_S10⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- S22: S holds [NOOP]
    rw [h] at hmemP
    obtain ⟨T, hP⟩ := hmemP
    simp only [S22, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mNOOP] := Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      have hq : q = "POPClient" := congrArg (fun m => m.1) hmem
      have hlab : lab = "NOOP" := congrArg (fun m => m.2) hmem
      have hS : S = "unit" := congrArg (fun m => m.3) hmem
      subst hq; subst hlab; subst hS
      exact (hfair i).2 "POPServer" "POPClient" "NOOP" "unit"
        ⟨S23, by rw [h]; exact t_S22_S23⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- S23: queues empty
    rw [h] at hmemP
    obtain ⟨T, hP⟩ := hmemP
    simp only [S23, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      (obtain ⟨Q', hQ⟩ := hdeq; simp [Queue.dequeue, Queue.dequeue.go] at hQ)
  · -- S24: C holds [OK]
    rw [h] at hmemP
    obtain ⟨T, hP⟩ := hmemP
    simp only [S24, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mOK] := Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      have hq : q = "POPServer" := congrArg (fun m => m.1) hmem
      have hlab : lab = "OK" := congrArg (fun m => m.2) hmem
      have hS : S = "unit" := congrArg (fun m => m.3) hmem
      subst hq; subst hlab; subst hS
      exact (hfair i).2 "POPClient" "POPServer" "OK" "unit"
        ⟨S10, by rw [h]; exact t_S24_S10⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- S25: S holds [QUIT]
    rw [h] at hmemP
    obtain ⟨T, hP⟩ := hmemP
    simp only [S25, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mQUIT] := Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      have hq : q = "POPClient" := congrArg (fun m => m.1) hmem
      have hlab : lab = "QUIT" := congrArg (fun m => m.2) hmem
      have hS : S = "unit" := congrArg (fun m => m.3) hmem
      subst hq; subst hlab; subst hS
      exact (hfair i).2 "POPServer" "POPClient" "QUIT" "unit"
        ⟨S26, by rw [h]; exact t_S25_S26⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- S26: queues empty
    rw [h] at hmemP
    obtain ⟨T, hP⟩ := hmemP
    simp only [S26, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      (obtain ⟨Q', hQ⟩ := hdeq; simp [Queue.dequeue, Queue.dequeue.go] at hQ)
  · -- S27: C holds [OK]
    rw [h] at hmemP
    obtain ⟨T, hP⟩ := hmemP
    simp only [S27, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mOK] := Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      have hq : q = "POPServer" := congrArg (fun m => m.1) hmem
      have hlab : lab = "OK" := congrArg (fun m => m.2) hmem
      have hS : S = "unit" := congrArg (fun m => m.3) hmem
      subst hq; subst hlab; subst hS
      exact (hfair i).2 "POPClient" "POPServer" "OK" "unit"
        ⟨S28, by rw [h]; exact t_S27_S28⟩
    · obtain ⟨Q', hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- S28: queues empty
    rw [h] at hmemP
    obtain ⟨T, hP⟩ := hmemP
    simp only [S28, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      (obtain ⟨Q', hQ⟩ := hdeq; simp [Queue.dequeue, Queue.dequeue.go] at hQ)


-- ============ Output-liveness: stuck states have no orphans ============
/-- Every reachable stuck network from `Net` has no orphans. -/
theorem popOL_stuck : ∀ (N' : Network), net_trans_star Net N' →
    IsStuckNetwork N' → NoOrphanMessages N' := by
  intro N' hStar hStuck
  have hR := popReach N' hStar
  rcases hR with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exfalso
    exact hStuck ⟨_, _, by trivial, t_S0_S1⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t_S1_S2⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t_S2_S3⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t_S3_S0⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t_S4_S5⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t_S5_S6⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t_S6_S7⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t_S7_S8⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t_S8_S0⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t_S9_S10⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t_S10_S11⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t_S11_S12⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t_S12_S13⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t_S13_S10⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t_S14_S15⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t_S15_S16⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t_S16_S10⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t_S17_S10⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t_S18_S19⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t_S19_S20⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t_S20_S10⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t_S21_S10⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t_S22_S23⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t_S23_S24⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t_S24_S10⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t_S25_S26⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t_S26_S27⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, t_S27_S28⟩
  · intro r T Q p lab S Q' hmem hQ
    simp only [S28, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      simp [Queue.dequeue, Queue.dequeue.go] at hQ

/-- `Net` is output-live: fair paths drain queues, stuck states are clean. -/
theorem Net_outputLive : IsOutputLiveNetwork Net :=
  ⟨popOL_inf, popOL_stuck⟩


end Pop3

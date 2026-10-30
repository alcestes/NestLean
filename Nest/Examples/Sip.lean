import Nest.SessionUtils
import Nest.SessionAdequacy
import Nest.Tests.PrunableTest
import Nest.Drainability
import Nest.Examples.ProofUtils
import Nest.MonitorLTSCo
import Nest.MonitorCoFun
import Nest.NoRec.NoRecToolkit

namespace Sip

/- Session types from the NEST P4 testbed:
   `NEST/nest/nest_scala/src/main/scala/examples/08_sip.scala`
   (Scala package `sip`; file `08_sip.scala` maps to this module since
   Lean module names may not start with a digit).
   Translated below are the three `lst_*` local session types
   (`lst_SIPClientA`, `lst_SIPClientB`, `lst_SIPProxy`; none uses
   recursion). Switch setup, IP rules, port checks and monitor wiring
   from `setup` are not session types.
   Translation conventions: `IntChoice` branches become
   `internalChoice` branches `(agent, label, sort, cont)`;
   `ExtChoice` branches become `externalChoice` branches
   `(label, sort, cont)`; `Rec`/`Var`/`End` become `tRec`/`tVar`/`tEnd`.
   Agents become roles, labels stay labels. The Scala types carry no payload
   sorts, so every branch uses the placeholder sort `"unit"`. -/

/-- `lst_SIPClientA`. -/
def SIPClientA : SessionType :=
  SessionType.internalChoice
    [("Proxy", "INVITE", "unit",
      SessionType.externalChoice "Proxy"
        [("Trying", "unit",
          SessionType.externalChoice "Proxy"
            [("Ringing", "unit",
              SessionType.externalChoice "Proxy"
                [("OK", "unit", SessionType.tEnd),
                 ("Error", "unit", SessionType.tEnd)]),
             ("Error", "unit", SessionType.tEnd)]),
         ("Error", "unit", SessionType.tEnd)])]

/-- `lst_SIPClientB`. -/
def SIPClientB : SessionType :=
  SessionType.externalChoice "Proxy"
    [("INVITE", "unit",
      SessionType.internalChoice
        [("Proxy", "Ringing", "unit",
          SessionType.internalChoice
            [("Proxy", "OK", "unit", SessionType.tEnd),
             ("Proxy", "Error", "unit", SessionType.tEnd)]),
         ("Proxy", "Error", "unit", SessionType.tEnd)])]

/-- `lst_SIPProxy`. -/
def SIPProxy : SessionType :=
  SessionType.externalChoice "ClientA"
    [("INVITE", "unit",
      SessionType.internalChoice
        [("ClientB", "INVITE", "unit",
          SessionType.internalChoice
            [("ClientA", "Trying", "unit",
              SessionType.externalChoice "ClientB"
                [("Ringing", "unit",
                  SessionType.internalChoice
                    [("ClientA", "Ringing", "unit",
                      SessionType.externalChoice "ClientB"
                        [("OK", "unit",
                          SessionType.internalChoice
                            [("ClientA", "OK", "unit", SessionType.tEnd)]),
                         ("Error", "unit",
                          SessionType.internalChoice
                            [("ClientA", "Error", "unit", SessionType.tEnd)])])]),
                 ("Error", "unit",
                  SessionType.internalChoice
                    [("ClientA", "Error", "unit", SessionType.tEnd)])])]),
          ("ClientA", "Error", "unit", SessionType.tEnd)])]

-- All three types are recursion-free: certified by the generic `NoRec` lemmas.
/-- `SIPClientA` is recursion-free. -/
theorem SIPClientA_norec : SIPClientA.NoRec := no_rec_bool_true (by decide)
/-- Deep adequacy of `SIPClientA`. -/
theorem SIPClientA_deep : Prunable [] SIPClientA :=
  norec_deep SIPClientA_norec []
/-- Monitorability of `SIPClientA`. -/
theorem SIPClientA_mon : Drainability.Monitorable SIPClientA :=
  norec_monitorable SIPClientA_norec

/-- `SIPClientB` is recursion-free. -/
theorem SIPClientB_norec : SIPClientB.NoRec := no_rec_bool_true (by decide)
/-- Deep adequacy of `SIPClientB`. -/
theorem SIPClientB_deep : Prunable [] SIPClientB :=
  norec_deep SIPClientB_norec []
/-- Monitorability of `SIPClientB`. -/
theorem SIPClientB_mon : Drainability.Monitorable SIPClientB :=
  norec_monitorable SIPClientB_norec

/-- `SIPProxy` is recursion-free. -/
theorem SIPProxy_norec : SIPProxy.NoRec := no_rec_bool_true (by decide)
/-- Deep adequacy of `SIPProxy`. -/
theorem SIPProxy_deep : Prunable [] SIPProxy :=
  norec_deep SIPProxy_norec []
/-- Monitorability of `SIPProxy`. -/
theorem SIPProxy_mon : Drainability.Monitorable SIPProxy :=
  norec_monitorable SIPProxy_norec

/-- Empty-queue network for the three SIP roles. -/
def Net : Network :=
  [("ClientA", (SIPClientA, [])),
   ("ClientB", (SIPClientB, [])),
   ("Proxy", (SIPProxy, []))]

/-- `Net` is well-formed. -/
theorem Net_wellFormed : Net.WellFormed := by
  refine ⟨by decide, ?_, Network.SenderClosed_of_all_nil (by decide)⟩
  intro x hx
  simp only [Net, List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact SIPClientA.wfCheck_sound (by decide)
  · exact SIPClientB.wfCheck_sound (by decide)
  · exact SIPProxy.wfCheck_sound (by decide)

/-- `Net` has no self-mention. -/
theorem Net_noSelf : Net.NoSelf := by
  apply Network.NoSelf_of_rolesOf
  intro x hx
  simp only [Net, List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl <;> decide

/-- `Net` contains every role occurring in its member types. -/
theorem Net_rolesPresent : Net.RolesPresent := by
  intro q T Q s hmem hOcc
  have hmemR : s ∈ rolesOf T := occurs_mem hOcc
  simp only [Net, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · simp only [SIPClientA, rolesOf, rolesOf.goInt, rolesOf.goExt,
      List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmemR
    have hs : s = "Proxy" := by tauto
    subst hs
    exact ⟨(SIPProxy, []), by decide⟩
  · simp only [SIPClientB, rolesOf, rolesOf.goInt, rolesOf.goExt,
      List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmemR
    have hs : s = "Proxy" := by tauto
    subst hs
    exact ⟨(SIPProxy, []), by decide⟩
  · simp only [SIPProxy, rolesOf, rolesOf.goInt, rolesOf.goExt,
      List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmemR
    have hAB : s = "ClientA" ∨ s = "ClientB" := by tauto
    rcases hAB with rfl | rfl
    · exact ⟨(SIPClientA, []), by decide⟩
    · exact ⟨(SIPClientB, []), by decide⟩

/-- `Net` admits consistent coinductive instrumentation. -/
theorem Net_consistent : ∃ MN, consistentInstrumentation_co Net = some MN :=
  exists_consistentInstrumentation_co_of_all_nil Net (by decide)

/-- The network is recursion-free, entrywise. -/
theorem Net_NoRec : Net.NoRec := by
  intro x hx
  simp only [Net, List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact SIPClientA_norec
  · exact SIPClientB_norec
  · exact SIPProxy_norec

/-- The infinite-path component is vacuous for this finite, recursion-free network. -/
theorem Net_outputLiveInfinite : IsOutputLiveInfinitePathNetwork Net :=
  norec_live_infinite_vacuous Net_NoRec Net_wellFormed

-- Residual session types (generated, hierarchical).
def SipT0 : SessionType :=
  SessionType.internalChoice [("ClientA", "Error", "unit", SessionType.tEnd)]
def SipT1 : SessionType :=
  SessionType.internalChoice [("ClientA", "OK", "unit", SessionType.tEnd)]
def SipT2 : SessionType :=
  SessionType.internalChoice [("Proxy", "OK", "unit", SessionType.tEnd), ("Proxy", "Error", "unit", SessionType.tEnd)]
def SipT3 : SessionType :=
  SessionType.externalChoice "Proxy" [("OK", "unit", SessionType.tEnd), ("Error", "unit", SessionType.tEnd)]
def SipT4 : SessionType :=
  SessionType.internalChoice [("Proxy", "Ringing", "unit", SipT2), ("Proxy", "Error", "unit", SessionType.tEnd)]
def SipT5 : SessionType :=
  SessionType.externalChoice "ClientB" [("OK", "unit", SipT1), ("Error", "unit", SipT0)]
def SipT6 : SessionType :=
  SessionType.externalChoice "Proxy" [("Ringing", "unit", SipT3), ("Error", "unit", SessionType.tEnd)]
def SipT7 : SessionType :=
  SessionType.internalChoice [("ClientA", "Ringing", "unit", SipT5)]
def SipT8 : SessionType :=
  SessionType.externalChoice "Proxy" [("Trying", "unit", SipT6), ("Error", "unit", SessionType.tEnd)]
def SipT9 : SessionType :=
  SessionType.externalChoice "ClientB" [("Ringing", "unit", SipT7), ("Error", "unit", SipT0)]
def SipT10 : SessionType :=
  SessionType.internalChoice [("ClientA", "Trying", "unit", SipT9)]
def SipT11 : SessionType :=
  SessionType.internalChoice [("ClientB", "INVITE", "unit", SipT10), ("ClientA", "Error", "unit", SessionType.tEnd)]

-- Queue message abbreviations (generated).
abbrev mClientAINVITE : QueueMessage := QueueMessage.msg "ClientA" "INVITE" "unit"
abbrev mClientBError : QueueMessage := QueueMessage.msg "ClientB" "Error" "unit"
abbrev mClientBOK : QueueMessage := QueueMessage.msg "ClientB" "OK" "unit"
abbrev mClientBRinging : QueueMessage := QueueMessage.msg "ClientB" "Ringing" "unit"
abbrev mProxyError : QueueMessage := QueueMessage.msg "Proxy" "Error" "unit"
abbrev mProxyINVITE : QueueMessage := QueueMessage.msg "Proxy" "INVITE" "unit"
abbrev mProxyOK : QueueMessage := QueueMessage.msg "Proxy" "OK" "unit"
abbrev mProxyRinging : QueueMessage := QueueMessage.msg "Proxy" "Ringing" "unit"
abbrev mProxyTrying : QueueMessage := QueueMessage.msg "Proxy" "Trying" "unit"

-- Reachable states (generated, replace order).
def S0 : Network := [("ClientA", (SIPClientA, [])), ("ClientB", (SIPClientB, [])), ("Proxy", (SIPProxy, []))]
def S1 : Network := [("Proxy", (SIPProxy, [mClientAINVITE])), ("ClientA", (SipT8, [])), ("ClientB", (SIPClientB, []))]
def S2 : Network := [("Proxy", (SipT11, [])), ("ClientA", (SipT8, [])), ("ClientB", (SIPClientB, []))]
def S3 : Network := [("ClientB", (SIPClientB, [mProxyINVITE])), ("Proxy", (SipT10, [])), ("ClientA", (SipT8, []))]
def S4 : Network := [("ClientA", (SipT8, [mProxyError])), ("Proxy", (SessionType.tEnd, [])), ("ClientB", (SIPClientB, []))]
def S5 : Network := [("ClientB", (SipT4, [])), ("Proxy", (SipT10, [])), ("ClientA", (SipT8, []))]
def S6 : Network := [("ClientA", (SipT8, [mProxyTrying])), ("Proxy", (SipT9, [])), ("ClientB", (SIPClientB, [mProxyINVITE]))]
def S7 : Network := [("ClientA", (SessionType.tEnd, [])), ("Proxy", (SessionType.tEnd, [])), ("ClientB", (SIPClientB, []))]
def S8 : Network := [("Proxy", (SipT10, [mClientBRinging])), ("ClientB", (SipT2, [])), ("ClientA", (SipT8, []))]
def S9 : Network := [("Proxy", (SipT10, [mClientBError])), ("ClientB", (SessionType.tEnd, [])), ("ClientA", (SipT8, []))]
def S10 : Network := [("ClientA", (SipT8, [mProxyTrying])), ("Proxy", (SipT9, [])), ("ClientB", (SipT4, []))]
def S11 : Network := [("ClientA", (SipT6, [])), ("Proxy", (SipT9, [])), ("ClientB", (SIPClientB, [mProxyINVITE]))]
def S12 : Network := [("ClientB", (SipT4, [])), ("ClientA", (SipT8, [mProxyTrying])), ("Proxy", (SipT9, []))]
def S13 : Network := [("ClientA", (SipT8, [mProxyTrying])), ("Proxy", (SipT9, [mClientBRinging])), ("ClientB", (SipT2, []))]
def S14 : Network := [("Proxy", (SipT10, [mClientBRinging, mClientBOK])), ("ClientB", (SessionType.tEnd, [])), ("ClientA", (SipT8, []))]
def S15 : Network := [("Proxy", (SipT10, [mClientBRinging, mClientBError])), ("ClientB", (SessionType.tEnd, [])), ("ClientA", (SipT8, []))]
def S16 : Network := [("ClientA", (SipT8, [mProxyTrying])), ("Proxy", (SipT9, [mClientBError])), ("ClientB", (SessionType.tEnd, []))]
def S17 : Network := [("ClientA", (SipT6, [])), ("Proxy", (SipT9, [])), ("ClientB", (SipT4, []))]
def S18 : Network := [("Proxy", (SipT9, [mClientBRinging])), ("ClientB", (SipT2, [])), ("ClientA", (SipT8, [mProxyTrying]))]
def S19 : Network := [("Proxy", (SipT9, [mClientBError])), ("ClientB", (SessionType.tEnd, [])), ("ClientA", (SipT8, [mProxyTrying]))]
def S20 : Network := [("ClientB", (SipT4, [])), ("ClientA", (SipT6, [])), ("Proxy", (SipT9, []))]
def S21 : Network := [("ClientA", (SipT6, [])), ("ClientB", (SipT4, [])), ("Proxy", (SipT9, []))]
def S22 : Network := [("ClientA", (SipT6, [])), ("Proxy", (SipT9, [mClientBRinging])), ("ClientB", (SipT2, []))]
def S23 : Network := [("Proxy", (SipT7, [])), ("ClientA", (SipT8, [mProxyTrying])), ("ClientB", (SipT2, []))]
def S24 : Network := [("Proxy", (SipT9, [mClientBRinging, mClientBOK])), ("ClientB", (SessionType.tEnd, [])), ("ClientA", (SipT8, [mProxyTrying]))]
def S25 : Network := [("Proxy", (SipT9, [mClientBRinging, mClientBError])), ("ClientB", (SessionType.tEnd, [])), ("ClientA", (SipT8, [mProxyTrying]))]
def S26 : Network := [("ClientA", (SipT8, [mProxyTrying])), ("Proxy", (SipT9, [mClientBRinging, mClientBOK])), ("ClientB", (SessionType.tEnd, []))]
def S27 : Network := [("ClientA", (SipT8, [mProxyTrying])), ("Proxy", (SipT9, [mClientBRinging, mClientBError])), ("ClientB", (SessionType.tEnd, []))]
def S28 : Network := [("ClientA", (SipT6, [])), ("Proxy", (SipT9, [mClientBError])), ("ClientB", (SessionType.tEnd, []))]
def S29 : Network := [("Proxy", (SipT0, [])), ("ClientA", (SipT8, [mProxyTrying])), ("ClientB", (SessionType.tEnd, []))]
def S30 : Network := [("Proxy", (SipT9, [mClientBRinging])), ("ClientB", (SipT2, [])), ("ClientA", (SipT6, []))]
def S31 : Network := [("Proxy", (SipT9, [mClientBError])), ("ClientB", (SessionType.tEnd, [])), ("ClientA", (SipT6, []))]
def S32 : Network := [("Proxy", (SipT7, [])), ("ClientB", (SipT2, [])), ("ClientA", (SipT8, [mProxyTrying]))]
def S33 : Network := [("Proxy", (SipT0, [])), ("ClientB", (SessionType.tEnd, [])), ("ClientA", (SipT8, [mProxyTrying]))]
def S34 : Network := [("Proxy", (SipT7, [])), ("ClientA", (SipT6, [])), ("ClientB", (SipT2, []))]
def S35 : Network := [("Proxy", (SipT9, [mClientBRinging, mClientBOK])), ("ClientB", (SessionType.tEnd, [])), ("ClientA", (SipT6, []))]
def S36 : Network := [("Proxy", (SipT9, [mClientBRinging, mClientBError])), ("ClientB", (SessionType.tEnd, [])), ("ClientA", (SipT6, []))]
def S37 : Network := [("ClientA", (SipT8, [mProxyTrying, mProxyRinging])), ("Proxy", (SipT5, [])), ("ClientB", (SipT2, []))]
def S38 : Network := [("ClientA", (SipT6, [])), ("Proxy", (SipT7, [])), ("ClientB", (SipT2, []))]
def S39 : Network := [("Proxy", (SipT7, [mClientBOK])), ("ClientB", (SessionType.tEnd, [])), ("ClientA", (SipT8, [mProxyTrying]))]
def S40 : Network := [("Proxy", (SipT7, [mClientBError])), ("ClientB", (SessionType.tEnd, [])), ("ClientA", (SipT8, [mProxyTrying]))]
def S41 : Network := [("ClientA", (SipT6, [])), ("Proxy", (SipT9, [mClientBRinging, mClientBOK])), ("ClientB", (SessionType.tEnd, []))]
def S42 : Network := [("ClientA", (SipT6, [])), ("Proxy", (SipT9, [mClientBRinging, mClientBError])), ("ClientB", (SessionType.tEnd, []))]
def S43 : Network := [("Proxy", (SipT7, [mClientBOK])), ("ClientA", (SipT8, [mProxyTrying])), ("ClientB", (SessionType.tEnd, []))]
def S44 : Network := [("Proxy", (SipT7, [mClientBError])), ("ClientA", (SipT8, [mProxyTrying])), ("ClientB", (SessionType.tEnd, []))]
def S45 : Network := [("Proxy", (SipT0, [])), ("ClientA", (SipT6, [])), ("ClientB", (SessionType.tEnd, []))]
def S46 : Network := [("ClientA", (SipT8, [mProxyTrying, mProxyError])), ("Proxy", (SessionType.tEnd, [])), ("ClientB", (SessionType.tEnd, []))]
def S47 : Network := [("ClientA", (SipT6, [])), ("Proxy", (SipT0, [])), ("ClientB", (SessionType.tEnd, []))]
def S48 : Network := [("Proxy", (SipT7, [])), ("ClientB", (SipT2, [])), ("ClientA", (SipT6, []))]
def S49 : Network := [("Proxy", (SipT0, [])), ("ClientB", (SessionType.tEnd, [])), ("ClientA", (SipT6, []))]
def S50 : Network := [("ClientA", (SipT6, [mProxyRinging])), ("Proxy", (SipT5, [])), ("ClientB", (SipT2, []))]
def S51 : Network := [("Proxy", (SipT7, [mClientBOK])), ("ClientB", (SessionType.tEnd, [])), ("ClientA", (SipT6, []))]
def S52 : Network := [("Proxy", (SipT7, [mClientBError])), ("ClientB", (SessionType.tEnd, [])), ("ClientA", (SipT6, []))]
def S53 : Network := [("Proxy", (SipT5, [mClientBOK])), ("ClientB", (SessionType.tEnd, [])), ("ClientA", (SipT8, [mProxyTrying, mProxyRinging]))]
def S54 : Network := [("Proxy", (SipT5, [mClientBError])), ("ClientB", (SessionType.tEnd, [])), ("ClientA", (SipT8, [mProxyTrying, mProxyRinging]))]
def S55 : Network := [("ClientA", (SipT8, [mProxyTrying, mProxyRinging])), ("Proxy", (SipT5, [mClientBOK])), ("ClientB", (SessionType.tEnd, []))]
def S56 : Network := [("ClientA", (SipT6, [])), ("Proxy", (SipT7, [mClientBOK])), ("ClientB", (SessionType.tEnd, []))]
def S57 : Network := [("ClientA", (SipT8, [mProxyTrying, mProxyRinging])), ("Proxy", (SipT5, [mClientBError])), ("ClientB", (SessionType.tEnd, []))]
def S58 : Network := [("ClientA", (SipT6, [])), ("Proxy", (SipT7, [mClientBError])), ("ClientB", (SessionType.tEnd, []))]
def S59 : Network := [("Proxy", (SipT7, [mClientBOK])), ("ClientA", (SipT6, [])), ("ClientB", (SessionType.tEnd, []))]
def S60 : Network := [("Proxy", (SipT7, [mClientBError])), ("ClientA", (SipT6, [])), ("ClientB", (SessionType.tEnd, []))]
def S61 : Network := [("ClientA", (SipT6, [mProxyError])), ("Proxy", (SessionType.tEnd, [])), ("ClientB", (SessionType.tEnd, []))]
def S62 : Network := [("ClientA", (SipT3, [])), ("Proxy", (SipT5, [])), ("ClientB", (SipT2, []))]
def S63 : Network := [("Proxy", (SipT5, [mClientBOK])), ("ClientB", (SessionType.tEnd, [])), ("ClientA", (SipT6, [mProxyRinging]))]
def S64 : Network := [("Proxy", (SipT5, [mClientBError])), ("ClientB", (SessionType.tEnd, [])), ("ClientA", (SipT6, [mProxyRinging]))]
def S65 : Network := [("ClientA", (SipT6, [mProxyRinging])), ("Proxy", (SipT5, [mClientBOK])), ("ClientB", (SessionType.tEnd, []))]
def S66 : Network := [("ClientA", (SipT6, [mProxyRinging])), ("Proxy", (SipT5, [mClientBError])), ("ClientB", (SessionType.tEnd, []))]
def S67 : Network := [("Proxy", (SipT1, [])), ("ClientB", (SessionType.tEnd, [])), ("ClientA", (SipT8, [mProxyTrying, mProxyRinging]))]
def S68 : Network := [("Proxy", (SipT0, [])), ("ClientB", (SessionType.tEnd, [])), ("ClientA", (SipT8, [mProxyTrying, mProxyRinging]))]
def S69 : Network := [("Proxy", (SipT1, [])), ("ClientA", (SipT8, [mProxyTrying, mProxyRinging])), ("ClientB", (SessionType.tEnd, []))]
def S70 : Network := [("Proxy", (SipT0, [])), ("ClientA", (SipT8, [mProxyTrying, mProxyRinging])), ("ClientB", (SessionType.tEnd, []))]
def S71 : Network := [("ClientA", (SessionType.tEnd, [])), ("Proxy", (SessionType.tEnd, [])), ("ClientB", (SessionType.tEnd, []))]
def S72 : Network := [("Proxy", (SipT5, [mClientBOK])), ("ClientB", (SessionType.tEnd, [])), ("ClientA", (SipT3, []))]
def S73 : Network := [("Proxy", (SipT5, [mClientBError])), ("ClientB", (SessionType.tEnd, [])), ("ClientA", (SipT3, []))]
def S74 : Network := [("Proxy", (SipT1, [])), ("ClientB", (SessionType.tEnd, [])), ("ClientA", (SipT6, [mProxyRinging]))]
def S75 : Network := [("ClientA", (SipT3, [])), ("Proxy", (SipT5, [mClientBOK])), ("ClientB", (SessionType.tEnd, []))]
def S76 : Network := [("Proxy", (SipT0, [])), ("ClientB", (SessionType.tEnd, [])), ("ClientA", (SipT6, [mProxyRinging]))]
def S77 : Network := [("ClientA", (SipT3, [])), ("Proxy", (SipT5, [mClientBError])), ("ClientB", (SessionType.tEnd, []))]
def S78 : Network := [("Proxy", (SipT1, [])), ("ClientA", (SipT6, [mProxyRinging])), ("ClientB", (SessionType.tEnd, []))]
def S79 : Network := [("Proxy", (SipT0, [])), ("ClientA", (SipT6, [mProxyRinging])), ("ClientB", (SessionType.tEnd, []))]
def S80 : Network := [("ClientA", (SipT8, [mProxyTrying, mProxyRinging, mProxyOK])), ("Proxy", (SessionType.tEnd, [])), ("ClientB", (SessionType.tEnd, []))]
def S81 : Network := [("ClientA", (SipT6, [mProxyRinging])), ("Proxy", (SipT1, [])), ("ClientB", (SessionType.tEnd, []))]
def S82 : Network := [("ClientA", (SipT8, [mProxyTrying, mProxyRinging, mProxyError])), ("Proxy", (SessionType.tEnd, [])), ("ClientB", (SessionType.tEnd, []))]
def S83 : Network := [("ClientA", (SipT6, [mProxyRinging])), ("Proxy", (SipT0, [])), ("ClientB", (SessionType.tEnd, []))]
def S84 : Network := [("Proxy", (SipT1, [])), ("ClientB", (SessionType.tEnd, [])), ("ClientA", (SipT3, []))]
def S85 : Network := [("Proxy", (SipT0, [])), ("ClientB", (SessionType.tEnd, [])), ("ClientA", (SipT3, []))]
def S86 : Network := [("ClientA", (SipT6, [mProxyRinging, mProxyOK])), ("Proxy", (SessionType.tEnd, [])), ("ClientB", (SessionType.tEnd, []))]
def S87 : Network := [("ClientA", (SipT3, [])), ("Proxy", (SipT1, [])), ("ClientB", (SessionType.tEnd, []))]
def S88 : Network := [("Proxy", (SipT1, [])), ("ClientA", (SipT3, [])), ("ClientB", (SessionType.tEnd, []))]
def S89 : Network := [("ClientA", (SipT6, [mProxyRinging, mProxyError])), ("Proxy", (SessionType.tEnd, [])), ("ClientB", (SessionType.tEnd, []))]
def S90 : Network := [("ClientA", (SipT3, [])), ("Proxy", (SipT0, [])), ("ClientB", (SessionType.tEnd, []))]
def S91 : Network := [("Proxy", (SipT0, [])), ("ClientA", (SipT3, [])), ("ClientB", (SessionType.tEnd, []))]
def S92 : Network := [("ClientA", (SipT3, [mProxyOK])), ("Proxy", (SessionType.tEnd, [])), ("ClientB", (SessionType.tEnd, []))]
def S93 : Network := [("ClientA", (SipT3, [mProxyError])), ("Proxy", (SessionType.tEnd, [])), ("ClientB", (SessionType.tEnd, []))]

-- Per-type step characterizations (generated).
theorem tEnd_no_out_sip {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans SessionType.tEnd (st_label.out p lab S) T') : False := by cases h
theorem tEnd_no_inp_sip {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans SessionType.tEnd (st_label.inp p lab S) T') : False := by cases h
theorem SIPClientA_no_inp_sip {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans SIPClientA (st_label.inp p lab S) T') : False := by
  unfold SIPClientA at h
  cases h
theorem SIPClientA_out_iff_sip {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans SIPClientA (st_label.out p lab S) T' →
    (p = "Proxy" ∧ lab = "INVITE" ∧ S = "unit" ∧ T' = SipT8) := by
  intro h
  unfold SIPClientA at h
  cases h with
  | intC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
    exact ⟨rfl, rfl, rfl, rfl⟩
theorem SIPClientB_no_out_sip {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans SIPClientB (st_label.out p lab S) T') : False := by
  unfold SIPClientB at h
  cases h
theorem SIPClientB_inp_iff_sip {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans SIPClientB (st_label.inp p lab S) T' →
    p = "Proxy" ∧ ((p = "Proxy" ∧ lab = "INVITE" ∧ S = "unit" ∧ T' = SipT4)) := by
  intro h
  unfold SIPClientB at h
  cases h with
  | extC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    exact ⟨rfl, ⟨rfl, rfl, rfl, rfl⟩⟩
theorem SIPProxy_no_out_sip {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans SIPProxy (st_label.out p lab S) T') : False := by
  unfold SIPProxy at h
  cases h
theorem SIPProxy_inp_iff_sip {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans SIPProxy (st_label.inp p lab S) T' →
    p = "ClientA" ∧ ((p = "ClientA" ∧ lab = "INVITE" ∧ S = "unit" ∧ T' = SipT11)) := by
  intro h
  unfold SIPProxy at h
  cases h with
  | extC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    exact ⟨rfl, ⟨rfl, rfl, rfl, rfl⟩⟩
theorem SipT0_no_inp_sip {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans SipT0 (st_label.inp p lab S) T') : False := by
  unfold SipT0 at h
  cases h
theorem SipT0_out_iff_sip {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans SipT0 (st_label.out p lab S) T' →
    (p = "ClientA" ∧ lab = "Error" ∧ S = "unit" ∧ T' = SessionType.tEnd) := by
  intro h
  unfold SipT0 at h
  cases h with
  | intC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
    exact ⟨rfl, rfl, rfl, rfl⟩
theorem SipT1_no_inp_sip {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans SipT1 (st_label.inp p lab S) T') : False := by
  unfold SipT1 at h
  cases h
theorem SipT1_out_iff_sip {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans SipT1 (st_label.out p lab S) T' →
    (p = "ClientA" ∧ lab = "OK" ∧ S = "unit" ∧ T' = SessionType.tEnd) := by
  intro h
  unfold SipT1 at h
  cases h with
  | intC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
    exact ⟨rfl, rfl, rfl, rfl⟩
theorem SipT2_no_inp_sip {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans SipT2 (st_label.inp p lab S) T') : False := by
  unfold SipT2 at h
  cases h
theorem SipT2_out_iff_sip {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans SipT2 (st_label.out p lab S) T' →
    (p = "Proxy" ∧ lab = "OK" ∧ S = "unit" ∧ T' = SessionType.tEnd) ∨ (p = "Proxy" ∧ lab = "Error" ∧ S = "unit" ∧ T' = SessionType.tEnd) := by
  intro h
  unfold SipT2 at h
  cases h with
  | intC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with h0 | h1
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := h0
      exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := h1
      exact Or.inr ⟨rfl, rfl, rfl, rfl⟩
theorem SipT3_no_out_sip {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans SipT3 (st_label.out p lab S) T') : False := by
  unfold SipT3 at h
  cases h
theorem SipT3_inp_iff_sip {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans SipT3 (st_label.inp p lab S) T' →
    p = "Proxy" ∧ ((p = "Proxy" ∧ lab = "OK" ∧ S = "unit" ∧ T' = SessionType.tEnd) ∨ (p = "Proxy" ∧ lab = "Error" ∧ S = "unit" ∧ T' = SessionType.tEnd)) := by
  intro h
  unfold SipT3 at h
  cases h with
  | extC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with h0 | h1
    · obtain ⟨rfl, rfl, rfl⟩ := h0
      exact ⟨rfl, Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩
    · obtain ⟨rfl, rfl, rfl⟩ := h1
      exact ⟨rfl, Or.inr ⟨rfl, rfl, rfl, rfl⟩⟩
theorem SipT4_no_inp_sip {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans SipT4 (st_label.inp p lab S) T') : False := by
  unfold SipT4 at h
  cases h
theorem SipT4_out_iff_sip {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans SipT4 (st_label.out p lab S) T' →
    (p = "Proxy" ∧ lab = "Ringing" ∧ S = "unit" ∧ T' = SipT2) ∨ (p = "Proxy" ∧ lab = "Error" ∧ S = "unit" ∧ T' = SessionType.tEnd) := by
  intro h
  unfold SipT4 at h
  cases h with
  | intC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with h0 | h1
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := h0
      exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := h1
      exact Or.inr ⟨rfl, rfl, rfl, rfl⟩
theorem SipT5_no_out_sip {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans SipT5 (st_label.out p lab S) T') : False := by
  unfold SipT5 at h
  cases h
theorem SipT5_inp_iff_sip {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans SipT5 (st_label.inp p lab S) T' →
    p = "ClientB" ∧ ((p = "ClientB" ∧ lab = "OK" ∧ S = "unit" ∧ T' = SipT1) ∨ (p = "ClientB" ∧ lab = "Error" ∧ S = "unit" ∧ T' = SipT0)) := by
  intro h
  unfold SipT5 at h
  cases h with
  | extC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with h0 | h1
    · obtain ⟨rfl, rfl, rfl⟩ := h0
      exact ⟨rfl, Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩
    · obtain ⟨rfl, rfl, rfl⟩ := h1
      exact ⟨rfl, Or.inr ⟨rfl, rfl, rfl, rfl⟩⟩
theorem SipT6_no_out_sip {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans SipT6 (st_label.out p lab S) T') : False := by
  unfold SipT6 at h
  cases h
theorem SipT6_inp_iff_sip {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans SipT6 (st_label.inp p lab S) T' →
    p = "Proxy" ∧ ((p = "Proxy" ∧ lab = "Ringing" ∧ S = "unit" ∧ T' = SipT3) ∨ (p = "Proxy" ∧ lab = "Error" ∧ S = "unit" ∧ T' = SessionType.tEnd)) := by
  intro h
  unfold SipT6 at h
  cases h with
  | extC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with h0 | h1
    · obtain ⟨rfl, rfl, rfl⟩ := h0
      exact ⟨rfl, Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩
    · obtain ⟨rfl, rfl, rfl⟩ := h1
      exact ⟨rfl, Or.inr ⟨rfl, rfl, rfl, rfl⟩⟩
theorem SipT7_no_inp_sip {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans SipT7 (st_label.inp p lab S) T') : False := by
  unfold SipT7 at h
  cases h
theorem SipT7_out_iff_sip {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans SipT7 (st_label.out p lab S) T' →
    (p = "ClientA" ∧ lab = "Ringing" ∧ S = "unit" ∧ T' = SipT5) := by
  intro h
  unfold SipT7 at h
  cases h with
  | intC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
    exact ⟨rfl, rfl, rfl, rfl⟩
theorem SipT8_no_out_sip {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans SipT8 (st_label.out p lab S) T') : False := by
  unfold SipT8 at h
  cases h
theorem SipT8_inp_iff_sip {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans SipT8 (st_label.inp p lab S) T' →
    p = "Proxy" ∧ ((p = "Proxy" ∧ lab = "Trying" ∧ S = "unit" ∧ T' = SipT6) ∨ (p = "Proxy" ∧ lab = "Error" ∧ S = "unit" ∧ T' = SessionType.tEnd)) := by
  intro h
  unfold SipT8 at h
  cases h with
  | extC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with h0 | h1
    · obtain ⟨rfl, rfl, rfl⟩ := h0
      exact ⟨rfl, Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩
    · obtain ⟨rfl, rfl, rfl⟩ := h1
      exact ⟨rfl, Or.inr ⟨rfl, rfl, rfl, rfl⟩⟩
theorem SipT9_no_out_sip {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans SipT9 (st_label.out p lab S) T') : False := by
  unfold SipT9 at h
  cases h
theorem SipT9_inp_iff_sip {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans SipT9 (st_label.inp p lab S) T' →
    p = "ClientB" ∧ ((p = "ClientB" ∧ lab = "Ringing" ∧ S = "unit" ∧ T' = SipT7) ∨ (p = "ClientB" ∧ lab = "Error" ∧ S = "unit" ∧ T' = SipT0)) := by
  intro h
  unfold SipT9 at h
  cases h with
  | extC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with h0 | h1
    · obtain ⟨rfl, rfl, rfl⟩ := h0
      exact ⟨rfl, Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩
    · obtain ⟨rfl, rfl, rfl⟩ := h1
      exact ⟨rfl, Or.inr ⟨rfl, rfl, rfl, rfl⟩⟩
theorem SipT10_no_inp_sip {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans SipT10 (st_label.inp p lab S) T') : False := by
  unfold SipT10 at h
  cases h
theorem SipT10_out_iff_sip {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans SipT10 (st_label.out p lab S) T' →
    (p = "ClientA" ∧ lab = "Trying" ∧ S = "unit" ∧ T' = SipT9) := by
  intro h
  unfold SipT10 at h
  cases h with
  | intC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
    exact ⟨rfl, rfl, rfl, rfl⟩
theorem SipT11_no_inp_sip {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans SipT11 (st_label.inp p lab S) T') : False := by
  unfold SipT11 at h
  cases h
theorem SipT11_out_iff_sip {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans SipT11 (st_label.out p lab S) T' →
    (p = "ClientB" ∧ lab = "INVITE" ∧ S = "unit" ∧ T' = SipT10) ∨ (p = "ClientA" ∧ lab = "Error" ∧ S = "unit" ∧ T' = SessionType.tEnd) := by
  intro h
  unfold SipT11 at h
  cases h with
  | intC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with h0 | h1
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := h0
      exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := h1
      exact Or.inr ⟨rfl, rfl, rfl, rfl⟩

theorem S0_step : ∀ (δ : net_label) (N' : Network),
    net_trans S0 δ N' → is_internal_net_label δ → N' = S1 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S0, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S0, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SIPClientA_out_iff_sip hST
          obtain ⟨heq, _, _, _⟩ := ho
          exact absurd heq (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SIPClientA_out_iff_sip hST
          obtain ⟨_, rfl, rfl, rfl⟩ := ho
          exact rfl
    · cases h_send with
      | send hST => exact absurd hST (fun h => SIPClientB_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SIPClientB_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SIPProxy_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SIPProxy_no_out_sip h)
    · exact absurd rfl hne

theorem S1_step : ∀ (δ : net_label) (N' : Network),
    net_trans S1 δ N' → is_internal_net_label δ → N' = S2 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S1, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SIPProxy_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        obtain ⟨_, rfl, rfl, rfl⟩ := hbr
        have hQe : Queue.dequeue [mClientAINVITE] (QueueMessage.msg "ClientA" "INVITE" "unit") = some [] := rfl
        rw [hQe] at hQ
        cases hQ
        exact rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S1, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SIPProxy_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SIPProxy_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SIPClientB_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SIPClientB_no_out_sip h)
    · exact absurd rfl hne

theorem S2_step : ∀ (δ : net_label) (N' : Network),
    net_trans S2 δ N' → is_internal_net_label δ → N' = S3 ∨ N' = S4 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S2, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S2, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT11_out_iff_sip hST
          rcases ho with h0 | h1
          · obtain ⟨heq, _, _, _⟩ := h0
            exact absurd heq (by decide)
          · obtain ⟨_, rfl, rfl, rfl⟩ := h1
            exact Or.inr (rfl)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT11_out_iff_sip hST
          rcases ho with h0 | h1
          · obtain ⟨_, rfl, rfl, rfl⟩ := h0
            exact Or.inl rfl
          · obtain ⟨heq, _, _, _⟩ := h1
            exact absurd heq (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SIPClientB_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SIPClientB_no_out_sip h)
    · exact absurd rfl hne

theorem S3_step : ∀ (δ : net_label) (N' : Network),
    net_trans S3 δ N' → is_internal_net_label δ → N' = S5 ∨ N' = S6 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S3, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SIPClientB_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        obtain ⟨_, rfl, rfl, rfl⟩ := hbr
        have hQe : Queue.dequeue [mProxyINVITE] (QueueMessage.msg "Proxy" "INVITE" "unit") = some [] := rfl
        rw [hQe] at hQ
        cases hQ
        exact Or.inl rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S3, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SIPClientB_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SIPClientB_no_out_sip h)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT10_out_iff_sip hST
          obtain ⟨heq, _, _, _⟩ := ho
          exact absurd heq (by decide)
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT10_out_iff_sip hST
          obtain ⟨_, rfl, rfl, rfl⟩ := ho
          exact Or.inr (rfl)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · exact absurd rfl hne

theorem S4_step : ∀ (δ : net_label) (N' : Network),
    net_trans S4 δ N' → is_internal_net_label δ → N' = S7 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S4, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT8_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mProxyError] (QueueMessage.msg "Proxy" "Trying" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mProxyError] (QueueMessage.msg "Proxy" "Error" "unit") = some [] := rfl
          rw [hQe] at hQ
          cases hQ
          exact rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S4, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SIPClientB_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SIPClientB_no_out_sip h)
    · exact absurd rfl hne

theorem S5_step : ∀ (δ : net_label) (N' : Network),
    net_trans S5 δ N' → is_internal_net_label δ → N' = S8 ∨ N' = S9 ∨ N' = S10 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S5, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S5, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT4_out_iff_sip hST
          rcases ho with h0 | h1
          · obtain ⟨_, rfl, rfl, rfl⟩ := h0
            exact Or.inl rfl
          · obtain ⟨_, rfl, rfl, rfl⟩ := h1
            exact Or.inr (Or.inl rfl)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT4_out_iff_sip hST
          rcases ho with h0 | h1
          · obtain ⟨heq, _, _, _⟩ := h0
            exact absurd heq (by decide)
          · obtain ⟨heq, _, _, _⟩ := h1
            exact absurd heq (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT10_out_iff_sip hST
          obtain ⟨heq, _, _, _⟩ := ho
          exact absurd heq (by decide)
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT10_out_iff_sip hST
          obtain ⟨_, rfl, rfl, rfl⟩ := ho
          exact Or.inr (Or.inr (rfl))
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · exact absurd rfl hne

theorem S6_step : ∀ (δ : net_label) (N' : Network),
    net_trans S6 δ N' → is_internal_net_label δ → N' = S11 ∨ N' = S12 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S6, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT8_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mProxyTrying] (QueueMessage.msg "Proxy" "Trying" "unit") = some [] := rfl
          rw [hQe] at hQ
          cases hQ
          exact Or.inl rfl
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mProxyTrying] (QueueMessage.msg "Proxy" "Error" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SIPClientB_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        obtain ⟨_, rfl, rfl, rfl⟩ := hbr
        have hQe : Queue.dequeue [mProxyINVITE] (QueueMessage.msg "Proxy" "INVITE" "unit") = some [] := rfl
        rw [hQe] at hQ
        cases hQ
        exact Or.inr (rfl)
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S6, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT9_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT9_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SIPClientB_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SIPClientB_no_out_sip h)
    · exact absurd rfl hne

theorem S7_no_step : ∀ (δ : net_label) (N' : Network),
    net_trans S7 δ N' → is_internal_net_label δ → False := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S7, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S7, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SIPClientB_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SIPClientB_no_out_sip h)
    · exact absurd rfl hne

theorem S8_step : ∀ (δ : net_label) (N' : Network),
    net_trans S8 δ N' → is_internal_net_label δ → N' = S13 ∨ N' = S14 ∨ N' = S15 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S8, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => exact absurd hST (fun h => SipT10_no_inp_sip h)
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S8, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT10_out_iff_sip hST
          obtain ⟨heq, _, _, _⟩ := ho
          exact absurd heq (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT10_out_iff_sip hST
          obtain ⟨_, rfl, rfl, rfl⟩ := ho
          exact Or.inl rfl
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT2_out_iff_sip hST
          rcases ho with h0 | h1
          · obtain ⟨_, rfl, rfl, rfl⟩ := h0
            exact Or.inr (Or.inl rfl)
          · obtain ⟨_, rfl, rfl, rfl⟩ := h1
            exact Or.inr (Or.inr (rfl))
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT2_out_iff_sip hST
          rcases ho with h0 | h1
          · obtain ⟨heq, _, _, _⟩ := h0
            exact absurd heq (by decide)
          · obtain ⟨heq, _, _, _⟩ := h1
            exact absurd heq (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · exact absurd rfl hne

theorem S9_step : ∀ (δ : net_label) (N' : Network),
    net_trans S9 δ N' → is_internal_net_label δ → N' = S16 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S9, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => exact absurd hST (fun h => SipT10_no_inp_sip h)
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S9, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT10_out_iff_sip hST
          obtain ⟨heq, _, _, _⟩ := ho
          exact absurd heq (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT10_out_iff_sip hST
          obtain ⟨_, rfl, rfl, rfl⟩ := ho
          exact rfl
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · exact absurd rfl hne

theorem S10_step : ∀ (δ : net_label) (N' : Network),
    net_trans S10 δ N' → is_internal_net_label δ → N' = S17 ∨ N' = S18 ∨ N' = S19 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S10, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT8_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mProxyTrying] (QueueMessage.msg "Proxy" "Trying" "unit") = some [] := rfl
          rw [hQe] at hQ
          cases hQ
          exact Or.inl rfl
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mProxyTrying] (QueueMessage.msg "Proxy" "Error" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S10, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT9_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT9_no_out_sip h)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT4_out_iff_sip hST
          rcases ho with h0 | h1
          · obtain ⟨heq, _, _, _⟩ := h0
            exact absurd heq (by decide)
          · obtain ⟨heq, _, _, _⟩ := h1
            exact absurd heq (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT4_out_iff_sip hST
          rcases ho with h0 | h1
          · obtain ⟨_, rfl, rfl, rfl⟩ := h0
            exact Or.inr (Or.inl rfl)
          · obtain ⟨_, rfl, rfl, rfl⟩ := h1
            exact Or.inr (Or.inr (rfl))
    · exact absurd rfl hne

theorem S11_step : ∀ (δ : net_label) (N' : Network),
    net_trans S11 δ N' → is_internal_net_label δ → N' = S20 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S11, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SIPClientB_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        obtain ⟨_, rfl, rfl, rfl⟩ := hbr
        have hQe : Queue.dequeue [mProxyINVITE] (QueueMessage.msg "Proxy" "INVITE" "unit") = some [] := rfl
        rw [hQe] at hQ
        cases hQ
        exact rfl
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S11, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT9_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT9_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SIPClientB_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SIPClientB_no_out_sip h)
    · exact absurd rfl hne

theorem S12_step : ∀ (δ : net_label) (N' : Network),
    net_trans S12 δ N' → is_internal_net_label δ → N' = S18 ∨ N' = S19 ∨ N' = S21 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S12, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT8_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mProxyTrying] (QueueMessage.msg "Proxy" "Trying" "unit") = some [] := rfl
          rw [hQe] at hQ
          cases hQ
          exact Or.inr (Or.inr (rfl))
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mProxyTrying] (QueueMessage.msg "Proxy" "Error" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S12, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT4_out_iff_sip hST
          rcases ho with h0 | h1
          · obtain ⟨heq, _, _, _⟩ := h0
            exact absurd heq (by decide)
          · obtain ⟨heq, _, _, _⟩ := h1
            exact absurd heq (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT4_out_iff_sip hST
          rcases ho with h0 | h1
          · obtain ⟨_, rfl, rfl, rfl⟩ := h0
            exact Or.inl rfl
          · obtain ⟨_, rfl, rfl, rfl⟩ := h1
            exact Or.inr (Or.inl rfl)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT9_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT9_no_out_sip h)
    · exact absurd rfl hne

theorem S13_step : ∀ (δ : net_label) (N' : Network),
    net_trans S13 δ N' → is_internal_net_label δ → N' = S22 ∨ N' = S23 ∨ N' = S24 ∨ N' = S25 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S13, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT8_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mProxyTrying] (QueueMessage.msg "Proxy" "Trying" "unit") = some [] := rfl
          rw [hQe] at hQ
          cases hQ
          exact Or.inl rfl
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mProxyTrying] (QueueMessage.msg "Proxy" "Error" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT9_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mClientBRinging] (QueueMessage.msg "ClientB" "Ringing" "unit") = some [] := rfl
          rw [hQe] at hQ
          cases hQ
          exact Or.inr (Or.inl rfl)
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mClientBRinging] (QueueMessage.msg "ClientB" "Error" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S13, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT9_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT9_no_out_sip h)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT2_out_iff_sip hST
          rcases ho with h0 | h1
          · obtain ⟨heq, _, _, _⟩ := h0
            exact absurd heq (by decide)
          · obtain ⟨heq, _, _, _⟩ := h1
            exact absurd heq (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT2_out_iff_sip hST
          rcases ho with h0 | h1
          · obtain ⟨_, rfl, rfl, rfl⟩ := h0
            exact Or.inr (Or.inr (Or.inl rfl))
          · obtain ⟨_, rfl, rfl, rfl⟩ := h1
            exact Or.inr (Or.inr (Or.inr (rfl)))
    · exact absurd rfl hne

theorem S14_step : ∀ (δ : net_label) (N' : Network),
    net_trans S14 δ N' → is_internal_net_label δ → N' = S26 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S14, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => exact absurd hST (fun h => SipT10_no_inp_sip h)
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S14, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT10_out_iff_sip hST
          obtain ⟨heq, _, _, _⟩ := ho
          exact absurd heq (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT10_out_iff_sip hST
          obtain ⟨_, rfl, rfl, rfl⟩ := ho
          exact rfl
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · exact absurd rfl hne

theorem S15_step : ∀ (δ : net_label) (N' : Network),
    net_trans S15 δ N' → is_internal_net_label δ → N' = S27 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S15, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => exact absurd hST (fun h => SipT10_no_inp_sip h)
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S15, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT10_out_iff_sip hST
          obtain ⟨heq, _, _, _⟩ := ho
          exact absurd heq (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT10_out_iff_sip hST
          obtain ⟨_, rfl, rfl, rfl⟩ := ho
          exact rfl
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · exact absurd rfl hne

theorem S16_step : ∀ (δ : net_label) (N' : Network),
    net_trans S16 δ N' → is_internal_net_label δ → N' = S28 ∨ N' = S29 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S16, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT8_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mProxyTrying] (QueueMessage.msg "Proxy" "Trying" "unit") = some [] := rfl
          rw [hQe] at hQ
          cases hQ
          exact Or.inl rfl
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mProxyTrying] (QueueMessage.msg "Proxy" "Error" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT9_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mClientBError] (QueueMessage.msg "ClientB" "Ringing" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mClientBError] (QueueMessage.msg "ClientB" "Error" "unit") = some [] := rfl
          rw [hQe] at hQ
          cases hQ
          exact Or.inr (rfl)
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S16, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT9_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT9_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne

theorem S17_step : ∀ (δ : net_label) (N' : Network),
    net_trans S17 δ N' → is_internal_net_label δ → N' = S30 ∨ N' = S31 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S17, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S17, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT9_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT9_no_out_sip h)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT4_out_iff_sip hST
          rcases ho with h0 | h1
          · obtain ⟨heq, _, _, _⟩ := h0
            exact absurd heq (by decide)
          · obtain ⟨heq, _, _, _⟩ := h1
            exact absurd heq (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT4_out_iff_sip hST
          rcases ho with h0 | h1
          · obtain ⟨_, rfl, rfl, rfl⟩ := h0
            exact Or.inl rfl
          · obtain ⟨_, rfl, rfl, rfl⟩ := h1
            exact Or.inr (rfl)
    · exact absurd rfl hne

theorem S18_step : ∀ (δ : net_label) (N' : Network),
    net_trans S18 δ N' → is_internal_net_label δ → N' = S32 ∨ N' = S24 ∨ N' = S25 ∨ N' = S22 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S18, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT9_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mClientBRinging] (QueueMessage.msg "ClientB" "Ringing" "unit") = some [] := rfl
          rw [hQe] at hQ
          cases hQ
          exact Or.inl rfl
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mClientBRinging] (QueueMessage.msg "ClientB" "Error" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT8_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mProxyTrying] (QueueMessage.msg "Proxy" "Trying" "unit") = some [] := rfl
          rw [hQe] at hQ
          cases hQ
          exact Or.inr (Or.inr (Or.inr (rfl)))
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mProxyTrying] (QueueMessage.msg "Proxy" "Error" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S18, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT9_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT9_no_out_sip h)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT2_out_iff_sip hST
          rcases ho with h0 | h1
          · obtain ⟨_, rfl, rfl, rfl⟩ := h0
            exact Or.inr (Or.inl rfl)
          · obtain ⟨_, rfl, rfl, rfl⟩ := h1
            exact Or.inr (Or.inr (Or.inl rfl))
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT2_out_iff_sip hST
          rcases ho with h0 | h1
          · obtain ⟨heq, _, _, _⟩ := h0
            exact absurd heq (by decide)
          · obtain ⟨heq, _, _, _⟩ := h1
            exact absurd heq (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · exact absurd rfl hne

theorem S19_step : ∀ (δ : net_label) (N' : Network),
    net_trans S19 δ N' → is_internal_net_label δ → N' = S33 ∨ N' = S28 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S19, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT9_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mClientBError] (QueueMessage.msg "ClientB" "Ringing" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mClientBError] (QueueMessage.msg "ClientB" "Error" "unit") = some [] := rfl
          rw [hQe] at hQ
          cases hQ
          exact Or.inl rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT8_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mProxyTrying] (QueueMessage.msg "Proxy" "Trying" "unit") = some [] := rfl
          rw [hQe] at hQ
          cases hQ
          exact Or.inr (rfl)
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mProxyTrying] (QueueMessage.msg "Proxy" "Error" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S19, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT9_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT9_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · exact absurd rfl hne

theorem S20_step : ∀ (δ : net_label) (N' : Network),
    net_trans S20 δ N' → is_internal_net_label δ → N' = S30 ∨ N' = S31 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S20, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S20, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT4_out_iff_sip hST
          rcases ho with h0 | h1
          · obtain ⟨heq, _, _, _⟩ := h0
            exact absurd heq (by decide)
          · obtain ⟨heq, _, _, _⟩ := h1
            exact absurd heq (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT4_out_iff_sip hST
          rcases ho with h0 | h1
          · obtain ⟨_, rfl, rfl, rfl⟩ := h0
            exact Or.inl rfl
          · obtain ⟨_, rfl, rfl, rfl⟩ := h1
            exact Or.inr (rfl)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT9_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT9_no_out_sip h)
    · exact absurd rfl hne

theorem S21_step : ∀ (δ : net_label) (N' : Network),
    net_trans S21 δ N' → is_internal_net_label δ → N' = S30 ∨ N' = S31 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S21, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S21, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT4_out_iff_sip hST
          rcases ho with h0 | h1
          · obtain ⟨heq, _, _, _⟩ := h0
            exact absurd heq (by decide)
          · obtain ⟨heq, _, _, _⟩ := h1
            exact absurd heq (by decide)
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT4_out_iff_sip hST
          rcases ho with h0 | h1
          · obtain ⟨_, rfl, rfl, rfl⟩ := h0
            exact Or.inl rfl
          · obtain ⟨_, rfl, rfl, rfl⟩ := h1
            exact Or.inr (rfl)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT9_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT9_no_out_sip h)
    · exact absurd rfl hne

theorem S22_step : ∀ (δ : net_label) (N' : Network),
    net_trans S22 δ N' → is_internal_net_label δ → N' = S34 ∨ N' = S35 ∨ N' = S36 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S22, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT9_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mClientBRinging] (QueueMessage.msg "ClientB" "Ringing" "unit") = some [] := rfl
          rw [hQe] at hQ
          cases hQ
          exact Or.inl rfl
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mClientBRinging] (QueueMessage.msg "ClientB" "Error" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S22, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT9_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT9_no_out_sip h)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT2_out_iff_sip hST
          rcases ho with h0 | h1
          · obtain ⟨heq, _, _, _⟩ := h0
            exact absurd heq (by decide)
          · obtain ⟨heq, _, _, _⟩ := h1
            exact absurd heq (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT2_out_iff_sip hST
          rcases ho with h0 | h1
          · obtain ⟨_, rfl, rfl, rfl⟩ := h0
            exact Or.inr (Or.inl rfl)
          · obtain ⟨_, rfl, rfl, rfl⟩ := h1
            exact Or.inr (Or.inr (rfl))
    · exact absurd rfl hne

theorem S23_step : ∀ (δ : net_label) (N' : Network),
    net_trans S23 δ N' → is_internal_net_label δ → N' = S37 ∨ N' = S38 ∨ N' = S39 ∨ N' = S40 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S23, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT8_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mProxyTrying] (QueueMessage.msg "Proxy" "Trying" "unit") = some [] := rfl
          rw [hQe] at hQ
          cases hQ
          exact Or.inr (Or.inl rfl)
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mProxyTrying] (QueueMessage.msg "Proxy" "Error" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S23, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT7_out_iff_sip hST
          obtain ⟨_, rfl, rfl, rfl⟩ := ho
          exact Or.inl rfl
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT7_out_iff_sip hST
          obtain ⟨heq, _, _, _⟩ := ho
          exact absurd heq (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT2_out_iff_sip hST
          rcases ho with h0 | h1
          · obtain ⟨_, rfl, rfl, rfl⟩ := h0
            exact Or.inr (Or.inr (Or.inl rfl))
          · obtain ⟨_, rfl, rfl, rfl⟩ := h1
            exact Or.inr (Or.inr (Or.inr (rfl)))
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT2_out_iff_sip hST
          rcases ho with h0 | h1
          · obtain ⟨heq, _, _, _⟩ := h0
            exact absurd heq (by decide)
          · obtain ⟨heq, _, _, _⟩ := h1
            exact absurd heq (by decide)
    · exact absurd rfl hne

theorem S24_step : ∀ (δ : net_label) (N' : Network),
    net_trans S24 δ N' → is_internal_net_label δ → N' = S39 ∨ N' = S41 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S24, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT9_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mClientBRinging, mClientBOK] (QueueMessage.msg "ClientB" "Ringing" "unit") = some [mClientBOK] := rfl
          rw [hQe] at hQ
          cases hQ
          exact Or.inl rfl
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mClientBRinging, mClientBOK] (QueueMessage.msg "ClientB" "Error" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT8_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mProxyTrying] (QueueMessage.msg "Proxy" "Trying" "unit") = some [] := rfl
          rw [hQe] at hQ
          cases hQ
          exact Or.inr (rfl)
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mProxyTrying] (QueueMessage.msg "Proxy" "Error" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S24, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT9_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT9_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · exact absurd rfl hne

theorem S25_step : ∀ (δ : net_label) (N' : Network),
    net_trans S25 δ N' → is_internal_net_label δ → N' = S40 ∨ N' = S42 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S25, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT9_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mClientBRinging, mClientBError] (QueueMessage.msg "ClientB" "Ringing" "unit") = some [mClientBError] := rfl
          rw [hQe] at hQ
          cases hQ
          exact Or.inl rfl
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mClientBRinging, mClientBError] (QueueMessage.msg "ClientB" "Error" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT8_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mProxyTrying] (QueueMessage.msg "Proxy" "Trying" "unit") = some [] := rfl
          rw [hQe] at hQ
          cases hQ
          exact Or.inr (rfl)
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mProxyTrying] (QueueMessage.msg "Proxy" "Error" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S25, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT9_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT9_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · exact absurd rfl hne

theorem S26_step : ∀ (δ : net_label) (N' : Network),
    net_trans S26 δ N' → is_internal_net_label δ → N' = S41 ∨ N' = S43 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S26, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT8_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mProxyTrying] (QueueMessage.msg "Proxy" "Trying" "unit") = some [] := rfl
          rw [hQe] at hQ
          cases hQ
          exact Or.inl rfl
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mProxyTrying] (QueueMessage.msg "Proxy" "Error" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT9_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mClientBRinging, mClientBOK] (QueueMessage.msg "ClientB" "Ringing" "unit") = some [mClientBOK] := rfl
          rw [hQe] at hQ
          cases hQ
          exact Or.inr (rfl)
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mClientBRinging, mClientBOK] (QueueMessage.msg "ClientB" "Error" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S26, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT9_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT9_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne

theorem S27_step : ∀ (δ : net_label) (N' : Network),
    net_trans S27 δ N' → is_internal_net_label δ → N' = S42 ∨ N' = S44 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S27, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT8_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mProxyTrying] (QueueMessage.msg "Proxy" "Trying" "unit") = some [] := rfl
          rw [hQe] at hQ
          cases hQ
          exact Or.inl rfl
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mProxyTrying] (QueueMessage.msg "Proxy" "Error" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT9_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mClientBRinging, mClientBError] (QueueMessage.msg "ClientB" "Ringing" "unit") = some [mClientBError] := rfl
          rw [hQe] at hQ
          cases hQ
          exact Or.inr (rfl)
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mClientBRinging, mClientBError] (QueueMessage.msg "ClientB" "Error" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S27, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT9_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT9_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne

theorem S28_step : ∀ (δ : net_label) (N' : Network),
    net_trans S28 δ N' → is_internal_net_label δ → N' = S45 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S28, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT9_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mClientBError] (QueueMessage.msg "ClientB" "Ringing" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mClientBError] (QueueMessage.msg "ClientB" "Error" "unit") = some [] := rfl
          rw [hQe] at hQ
          cases hQ
          exact rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S28, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT9_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT9_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne

theorem S29_step : ∀ (δ : net_label) (N' : Network),
    net_trans S29 δ N' → is_internal_net_label δ → N' = S46 ∨ N' = S47 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S29, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT8_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mProxyTrying] (QueueMessage.msg "Proxy" "Trying" "unit") = some [] := rfl
          rw [hQe] at hQ
          cases hQ
          exact Or.inr (rfl)
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mProxyTrying] (QueueMessage.msg "Proxy" "Error" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S29, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT0_out_iff_sip hST
          obtain ⟨_, rfl, rfl, rfl⟩ := ho
          exact Or.inl rfl
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT0_out_iff_sip hST
          obtain ⟨heq, _, _, _⟩ := ho
          exact absurd heq (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne

theorem S30_step : ∀ (δ : net_label) (N' : Network),
    net_trans S30 δ N' → is_internal_net_label δ → N' = S48 ∨ N' = S35 ∨ N' = S36 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S30, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT9_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mClientBRinging] (QueueMessage.msg "ClientB" "Ringing" "unit") = some [] := rfl
          rw [hQe] at hQ
          cases hQ
          exact Or.inl rfl
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mClientBRinging] (QueueMessage.msg "ClientB" "Error" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S30, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT9_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT9_no_out_sip h)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT2_out_iff_sip hST
          rcases ho with h0 | h1
          · obtain ⟨_, rfl, rfl, rfl⟩ := h0
            exact Or.inr (Or.inl rfl)
          · obtain ⟨_, rfl, rfl, rfl⟩ := h1
            exact Or.inr (Or.inr (rfl))
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT2_out_iff_sip hST
          rcases ho with h0 | h1
          · obtain ⟨heq, _, _, _⟩ := h0
            exact absurd heq (by decide)
          · obtain ⟨heq, _, _, _⟩ := h1
            exact absurd heq (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · exact absurd rfl hne

theorem S31_step : ∀ (δ : net_label) (N' : Network),
    net_trans S31 δ N' → is_internal_net_label δ → N' = S49 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S31, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT9_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mClientBError] (QueueMessage.msg "ClientB" "Ringing" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mClientBError] (QueueMessage.msg "ClientB" "Error" "unit") = some [] := rfl
          rw [hQe] at hQ
          cases hQ
          exact rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S31, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT9_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT9_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · exact absurd rfl hne

theorem S32_step : ∀ (δ : net_label) (N' : Network),
    net_trans S32 δ N' → is_internal_net_label δ → N' = S37 ∨ N' = S39 ∨ N' = S40 ∨ N' = S38 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S32, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT8_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mProxyTrying] (QueueMessage.msg "Proxy" "Trying" "unit") = some [] := rfl
          rw [hQe] at hQ
          cases hQ
          exact Or.inr (Or.inr (Or.inr (rfl)))
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mProxyTrying] (QueueMessage.msg "Proxy" "Error" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S32, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT7_out_iff_sip hST
          obtain ⟨heq, _, _, _⟩ := ho
          exact absurd heq (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT7_out_iff_sip hST
          obtain ⟨_, rfl, rfl, rfl⟩ := ho
          exact Or.inl rfl
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT2_out_iff_sip hST
          rcases ho with h0 | h1
          · obtain ⟨_, rfl, rfl, rfl⟩ := h0
            exact Or.inr (Or.inl rfl)
          · obtain ⟨_, rfl, rfl, rfl⟩ := h1
            exact Or.inr (Or.inr (Or.inl rfl))
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT2_out_iff_sip hST
          rcases ho with h0 | h1
          · obtain ⟨heq, _, _, _⟩ := h0
            exact absurd heq (by decide)
          · obtain ⟨heq, _, _, _⟩ := h1
            exact absurd heq (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · exact absurd rfl hne

theorem S33_step : ∀ (δ : net_label) (N' : Network),
    net_trans S33 δ N' → is_internal_net_label δ → N' = S46 ∨ N' = S47 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S33, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT8_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mProxyTrying] (QueueMessage.msg "Proxy" "Trying" "unit") = some [] := rfl
          rw [hQe] at hQ
          cases hQ
          exact Or.inr (rfl)
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mProxyTrying] (QueueMessage.msg "Proxy" "Error" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S33, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT0_out_iff_sip hST
          obtain ⟨heq, _, _, _⟩ := ho
          exact absurd heq (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT0_out_iff_sip hST
          obtain ⟨_, rfl, rfl, rfl⟩ := ho
          exact Or.inl rfl
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · exact absurd rfl hne

theorem S34_step : ∀ (δ : net_label) (N' : Network),
    net_trans S34 δ N' → is_internal_net_label δ → N' = S50 ∨ N' = S51 ∨ N' = S52 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S34, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S34, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT7_out_iff_sip hST
          obtain ⟨_, rfl, rfl, rfl⟩ := ho
          exact Or.inl rfl
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT7_out_iff_sip hST
          obtain ⟨heq, _, _, _⟩ := ho
          exact absurd heq (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT2_out_iff_sip hST
          rcases ho with h0 | h1
          · obtain ⟨_, rfl, rfl, rfl⟩ := h0
            exact Or.inr (Or.inl rfl)
          · obtain ⟨_, rfl, rfl, rfl⟩ := h1
            exact Or.inr (Or.inr (rfl))
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT2_out_iff_sip hST
          rcases ho with h0 | h1
          · obtain ⟨heq, _, _, _⟩ := h0
            exact absurd heq (by decide)
          · obtain ⟨heq, _, _, _⟩ := h1
            exact absurd heq (by decide)
    · exact absurd rfl hne

theorem S35_step : ∀ (δ : net_label) (N' : Network),
    net_trans S35 δ N' → is_internal_net_label δ → N' = S51 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S35, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT9_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mClientBRinging, mClientBOK] (QueueMessage.msg "ClientB" "Ringing" "unit") = some [mClientBOK] := rfl
          rw [hQe] at hQ
          cases hQ
          exact rfl
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mClientBRinging, mClientBOK] (QueueMessage.msg "ClientB" "Error" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S35, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT9_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT9_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · exact absurd rfl hne

theorem S36_step : ∀ (δ : net_label) (N' : Network),
    net_trans S36 δ N' → is_internal_net_label δ → N' = S52 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S36, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT9_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mClientBRinging, mClientBError] (QueueMessage.msg "ClientB" "Ringing" "unit") = some [mClientBError] := rfl
          rw [hQe] at hQ
          cases hQ
          exact rfl
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mClientBRinging, mClientBError] (QueueMessage.msg "ClientB" "Error" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S36, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT9_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT9_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · exact absurd rfl hne

theorem S37_step : ∀ (δ : net_label) (N' : Network),
    net_trans S37 δ N' → is_internal_net_label δ → N' = S50 ∨ N' = S53 ∨ N' = S54 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S37, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT8_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mProxyTrying, mProxyRinging] (QueueMessage.msg "Proxy" "Trying" "unit") = some [mProxyRinging] := rfl
          rw [hQe] at hQ
          cases hQ
          exact Or.inl rfl
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mProxyTrying, mProxyRinging] (QueueMessage.msg "Proxy" "Error" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S37, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT5_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT5_no_out_sip h)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT2_out_iff_sip hST
          rcases ho with h0 | h1
          · obtain ⟨heq, _, _, _⟩ := h0
            exact absurd heq (by decide)
          · obtain ⟨heq, _, _, _⟩ := h1
            exact absurd heq (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT2_out_iff_sip hST
          rcases ho with h0 | h1
          · obtain ⟨_, rfl, rfl, rfl⟩ := h0
            exact Or.inr (Or.inl rfl)
          · obtain ⟨_, rfl, rfl, rfl⟩ := h1
            exact Or.inr (Or.inr (rfl))
    · exact absurd rfl hne

theorem S38_step : ∀ (δ : net_label) (N' : Network),
    net_trans S38 δ N' → is_internal_net_label δ → N' = S50 ∨ N' = S51 ∨ N' = S52 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S38, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S38, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT7_out_iff_sip hST
          obtain ⟨_, rfl, rfl, rfl⟩ := ho
          exact Or.inl rfl
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT7_out_iff_sip hST
          obtain ⟨heq, _, _, _⟩ := ho
          exact absurd heq (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT2_out_iff_sip hST
          rcases ho with h0 | h1
          · obtain ⟨heq, _, _, _⟩ := h0
            exact absurd heq (by decide)
          · obtain ⟨heq, _, _, _⟩ := h1
            exact absurd heq (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT2_out_iff_sip hST
          rcases ho with h0 | h1
          · obtain ⟨_, rfl, rfl, rfl⟩ := h0
            exact Or.inr (Or.inl rfl)
          · obtain ⟨_, rfl, rfl, rfl⟩ := h1
            exact Or.inr (Or.inr (rfl))
    · exact absurd rfl hne

theorem S39_step : ∀ (δ : net_label) (N' : Network),
    net_trans S39 δ N' → is_internal_net_label δ → N' = S55 ∨ N' = S56 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S39, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => exact absurd hST (fun h => SipT7_no_inp_sip h)
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT8_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mProxyTrying] (QueueMessage.msg "Proxy" "Trying" "unit") = some [] := rfl
          rw [hQe] at hQ
          cases hQ
          exact Or.inr (rfl)
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mProxyTrying] (QueueMessage.msg "Proxy" "Error" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S39, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT7_out_iff_sip hST
          obtain ⟨heq, _, _, _⟩ := ho
          exact absurd heq (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT7_out_iff_sip hST
          obtain ⟨_, rfl, rfl, rfl⟩ := ho
          exact Or.inl rfl
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · exact absurd rfl hne

theorem S40_step : ∀ (δ : net_label) (N' : Network),
    net_trans S40 δ N' → is_internal_net_label δ → N' = S57 ∨ N' = S58 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S40, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => exact absurd hST (fun h => SipT7_no_inp_sip h)
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT8_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mProxyTrying] (QueueMessage.msg "Proxy" "Trying" "unit") = some [] := rfl
          rw [hQe] at hQ
          cases hQ
          exact Or.inr (rfl)
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mProxyTrying] (QueueMessage.msg "Proxy" "Error" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S40, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT7_out_iff_sip hST
          obtain ⟨heq, _, _, _⟩ := ho
          exact absurd heq (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT7_out_iff_sip hST
          obtain ⟨_, rfl, rfl, rfl⟩ := ho
          exact Or.inl rfl
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · exact absurd rfl hne

theorem S41_step : ∀ (δ : net_label) (N' : Network),
    net_trans S41 δ N' → is_internal_net_label δ → N' = S59 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S41, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT9_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mClientBRinging, mClientBOK] (QueueMessage.msg "ClientB" "Ringing" "unit") = some [mClientBOK] := rfl
          rw [hQe] at hQ
          cases hQ
          exact rfl
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mClientBRinging, mClientBOK] (QueueMessage.msg "ClientB" "Error" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S41, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT9_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT9_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne

theorem S42_step : ∀ (δ : net_label) (N' : Network),
    net_trans S42 δ N' → is_internal_net_label δ → N' = S60 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S42, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT9_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mClientBRinging, mClientBError] (QueueMessage.msg "ClientB" "Ringing" "unit") = some [mClientBError] := rfl
          rw [hQe] at hQ
          cases hQ
          exact rfl
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mClientBRinging, mClientBError] (QueueMessage.msg "ClientB" "Error" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S42, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT9_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT9_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne

theorem S43_step : ∀ (δ : net_label) (N' : Network),
    net_trans S43 δ N' → is_internal_net_label δ → N' = S55 ∨ N' = S56 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S43, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => exact absurd hST (fun h => SipT7_no_inp_sip h)
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT8_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mProxyTrying] (QueueMessage.msg "Proxy" "Trying" "unit") = some [] := rfl
          rw [hQe] at hQ
          cases hQ
          exact Or.inr (rfl)
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mProxyTrying] (QueueMessage.msg "Proxy" "Error" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S43, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT7_out_iff_sip hST
          obtain ⟨_, rfl, rfl, rfl⟩ := ho
          exact Or.inl rfl
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT7_out_iff_sip hST
          obtain ⟨heq, _, _, _⟩ := ho
          exact absurd heq (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne

theorem S44_step : ∀ (δ : net_label) (N' : Network),
    net_trans S44 δ N' → is_internal_net_label δ → N' = S57 ∨ N' = S58 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S44, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => exact absurd hST (fun h => SipT7_no_inp_sip h)
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT8_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mProxyTrying] (QueueMessage.msg "Proxy" "Trying" "unit") = some [] := rfl
          rw [hQe] at hQ
          cases hQ
          exact Or.inr (rfl)
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mProxyTrying] (QueueMessage.msg "Proxy" "Error" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S44, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT7_out_iff_sip hST
          obtain ⟨_, rfl, rfl, rfl⟩ := ho
          exact Or.inl rfl
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT7_out_iff_sip hST
          obtain ⟨heq, _, _, _⟩ := ho
          exact absurd heq (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne

theorem S45_step : ∀ (δ : net_label) (N' : Network),
    net_trans S45 δ N' → is_internal_net_label δ → N' = S61 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S45, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S45, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT0_out_iff_sip hST
          obtain ⟨_, rfl, rfl, rfl⟩ := ho
          exact rfl
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT0_out_iff_sip hST
          obtain ⟨heq, _, _, _⟩ := ho
          exact absurd heq (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne

theorem S46_step : ∀ (δ : net_label) (N' : Network),
    net_trans S46 δ N' → is_internal_net_label δ → N' = S61 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S46, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT8_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mProxyTrying, mProxyError] (QueueMessage.msg "Proxy" "Trying" "unit") = some [mProxyError] := rfl
          rw [hQe] at hQ
          cases hQ
          exact rfl
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mProxyTrying, mProxyError] (QueueMessage.msg "Proxy" "Error" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S46, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne

theorem S47_step : ∀ (δ : net_label) (N' : Network),
    net_trans S47 δ N' → is_internal_net_label δ → N' = S61 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S47, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S47, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT0_out_iff_sip hST
          obtain ⟨_, rfl, rfl, rfl⟩ := ho
          exact rfl
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT0_out_iff_sip hST
          obtain ⟨heq, _, _, _⟩ := ho
          exact absurd heq (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne

theorem S48_step : ∀ (δ : net_label) (N' : Network),
    net_trans S48 δ N' → is_internal_net_label δ → N' = S50 ∨ N' = S51 ∨ N' = S52 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S48, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S48, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT7_out_iff_sip hST
          obtain ⟨heq, _, _, _⟩ := ho
          exact absurd heq (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT7_out_iff_sip hST
          obtain ⟨_, rfl, rfl, rfl⟩ := ho
          exact Or.inl rfl
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT2_out_iff_sip hST
          rcases ho with h0 | h1
          · obtain ⟨_, rfl, rfl, rfl⟩ := h0
            exact Or.inr (Or.inl rfl)
          · obtain ⟨_, rfl, rfl, rfl⟩ := h1
            exact Or.inr (Or.inr (rfl))
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT2_out_iff_sip hST
          rcases ho with h0 | h1
          · obtain ⟨heq, _, _, _⟩ := h0
            exact absurd heq (by decide)
          · obtain ⟨heq, _, _, _⟩ := h1
            exact absurd heq (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · exact absurd rfl hne

theorem S49_step : ∀ (δ : net_label) (N' : Network),
    net_trans S49 δ N' → is_internal_net_label δ → N' = S61 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S49, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S49, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT0_out_iff_sip hST
          obtain ⟨heq, _, _, _⟩ := ho
          exact absurd heq (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT0_out_iff_sip hST
          obtain ⟨_, rfl, rfl, rfl⟩ := ho
          exact rfl
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · exact absurd rfl hne

theorem S50_step : ∀ (δ : net_label) (N' : Network),
    net_trans S50 δ N' → is_internal_net_label δ → N' = S62 ∨ N' = S63 ∨ N' = S64 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S50, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT6_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mProxyRinging] (QueueMessage.msg "Proxy" "Ringing" "unit") = some [] := rfl
          rw [hQe] at hQ
          cases hQ
          exact Or.inl rfl
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mProxyRinging] (QueueMessage.msg "Proxy" "Error" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S50, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT5_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT5_no_out_sip h)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT2_out_iff_sip hST
          rcases ho with h0 | h1
          · obtain ⟨heq, _, _, _⟩ := h0
            exact absurd heq (by decide)
          · obtain ⟨heq, _, _, _⟩ := h1
            exact absurd heq (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT2_out_iff_sip hST
          rcases ho with h0 | h1
          · obtain ⟨_, rfl, rfl, rfl⟩ := h0
            exact Or.inr (Or.inl rfl)
          · obtain ⟨_, rfl, rfl, rfl⟩ := h1
            exact Or.inr (Or.inr (rfl))
    · exact absurd rfl hne

theorem S51_step : ∀ (δ : net_label) (N' : Network),
    net_trans S51 δ N' → is_internal_net_label δ → N' = S65 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S51, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => exact absurd hST (fun h => SipT7_no_inp_sip h)
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S51, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT7_out_iff_sip hST
          obtain ⟨heq, _, _, _⟩ := ho
          exact absurd heq (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT7_out_iff_sip hST
          obtain ⟨_, rfl, rfl, rfl⟩ := ho
          exact rfl
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · exact absurd rfl hne

theorem S52_step : ∀ (δ : net_label) (N' : Network),
    net_trans S52 δ N' → is_internal_net_label δ → N' = S66 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S52, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => exact absurd hST (fun h => SipT7_no_inp_sip h)
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S52, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT7_out_iff_sip hST
          obtain ⟨heq, _, _, _⟩ := ho
          exact absurd heq (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT7_out_iff_sip hST
          obtain ⟨_, rfl, rfl, rfl⟩ := ho
          exact rfl
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · exact absurd rfl hne

theorem S53_step : ∀ (δ : net_label) (N' : Network),
    net_trans S53 δ N' → is_internal_net_label δ → N' = S67 ∨ N' = S65 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S53, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT5_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mClientBOK] (QueueMessage.msg "ClientB" "OK" "unit") = some [] := rfl
          rw [hQe] at hQ
          cases hQ
          exact Or.inl rfl
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mClientBOK] (QueueMessage.msg "ClientB" "Error" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT8_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mProxyTrying, mProxyRinging] (QueueMessage.msg "Proxy" "Trying" "unit") = some [mProxyRinging] := rfl
          rw [hQe] at hQ
          cases hQ
          exact Or.inr (rfl)
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mProxyTrying, mProxyRinging] (QueueMessage.msg "Proxy" "Error" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S53, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT5_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT5_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · exact absurd rfl hne

theorem S54_step : ∀ (δ : net_label) (N' : Network),
    net_trans S54 δ N' → is_internal_net_label δ → N' = S68 ∨ N' = S66 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S54, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT5_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mClientBError] (QueueMessage.msg "ClientB" "OK" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mClientBError] (QueueMessage.msg "ClientB" "Error" "unit") = some [] := rfl
          rw [hQe] at hQ
          cases hQ
          exact Or.inl rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT8_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mProxyTrying, mProxyRinging] (QueueMessage.msg "Proxy" "Trying" "unit") = some [mProxyRinging] := rfl
          rw [hQe] at hQ
          cases hQ
          exact Or.inr (rfl)
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mProxyTrying, mProxyRinging] (QueueMessage.msg "Proxy" "Error" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S54, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT5_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT5_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · exact absurd rfl hne

theorem S55_step : ∀ (δ : net_label) (N' : Network),
    net_trans S55 δ N' → is_internal_net_label δ → N' = S65 ∨ N' = S69 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S55, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT8_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mProxyTrying, mProxyRinging] (QueueMessage.msg "Proxy" "Trying" "unit") = some [mProxyRinging] := rfl
          rw [hQe] at hQ
          cases hQ
          exact Or.inl rfl
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mProxyTrying, mProxyRinging] (QueueMessage.msg "Proxy" "Error" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT5_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mClientBOK] (QueueMessage.msg "ClientB" "OK" "unit") = some [] := rfl
          rw [hQe] at hQ
          cases hQ
          exact Or.inr (rfl)
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mClientBOK] (QueueMessage.msg "ClientB" "Error" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S55, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT5_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT5_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne

theorem S56_step : ∀ (δ : net_label) (N' : Network),
    net_trans S56 δ N' → is_internal_net_label δ → N' = S65 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S56, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => exact absurd hST (fun h => SipT7_no_inp_sip h)
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S56, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT7_out_iff_sip hST
          obtain ⟨_, rfl, rfl, rfl⟩ := ho
          exact rfl
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT7_out_iff_sip hST
          obtain ⟨heq, _, _, _⟩ := ho
          exact absurd heq (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne

theorem S57_step : ∀ (δ : net_label) (N' : Network),
    net_trans S57 δ N' → is_internal_net_label δ → N' = S66 ∨ N' = S70 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S57, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT8_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mProxyTrying, mProxyRinging] (QueueMessage.msg "Proxy" "Trying" "unit") = some [mProxyRinging] := rfl
          rw [hQe] at hQ
          cases hQ
          exact Or.inl rfl
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mProxyTrying, mProxyRinging] (QueueMessage.msg "Proxy" "Error" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT5_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mClientBError] (QueueMessage.msg "ClientB" "OK" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mClientBError] (QueueMessage.msg "ClientB" "Error" "unit") = some [] := rfl
          rw [hQe] at hQ
          cases hQ
          exact Or.inr (rfl)
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S57, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT5_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT5_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne

theorem S58_step : ∀ (δ : net_label) (N' : Network),
    net_trans S58 δ N' → is_internal_net_label δ → N' = S66 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S58, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => exact absurd hST (fun h => SipT7_no_inp_sip h)
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S58, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT7_out_iff_sip hST
          obtain ⟨_, rfl, rfl, rfl⟩ := ho
          exact rfl
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT7_out_iff_sip hST
          obtain ⟨heq, _, _, _⟩ := ho
          exact absurd heq (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne

theorem S59_step : ∀ (δ : net_label) (N' : Network),
    net_trans S59 δ N' → is_internal_net_label δ → N' = S65 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S59, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => exact absurd hST (fun h => SipT7_no_inp_sip h)
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S59, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT7_out_iff_sip hST
          obtain ⟨_, rfl, rfl, rfl⟩ := ho
          exact rfl
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT7_out_iff_sip hST
          obtain ⟨heq, _, _, _⟩ := ho
          exact absurd heq (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne

theorem S60_step : ∀ (δ : net_label) (N' : Network),
    net_trans S60 δ N' → is_internal_net_label δ → N' = S66 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S60, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => exact absurd hST (fun h => SipT7_no_inp_sip h)
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S60, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT7_out_iff_sip hST
          obtain ⟨_, rfl, rfl, rfl⟩ := ho
          exact rfl
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT7_out_iff_sip hST
          obtain ⟨heq, _, _, _⟩ := ho
          exact absurd heq (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne

theorem S61_step : ∀ (δ : net_label) (N' : Network),
    net_trans S61 δ N' → is_internal_net_label δ → N' = S71 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S61, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT6_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mProxyError] (QueueMessage.msg "Proxy" "Ringing" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mProxyError] (QueueMessage.msg "Proxy" "Error" "unit") = some [] := rfl
          rw [hQe] at hQ
          cases hQ
          exact rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S61, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne

theorem S62_step : ∀ (δ : net_label) (N' : Network),
    net_trans S62 δ N' → is_internal_net_label δ → N' = S72 ∨ N' = S73 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S62, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S62, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT3_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT3_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT5_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT5_no_out_sip h)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT2_out_iff_sip hST
          rcases ho with h0 | h1
          · obtain ⟨heq, _, _, _⟩ := h0
            exact absurd heq (by decide)
          · obtain ⟨heq, _, _, _⟩ := h1
            exact absurd heq (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT2_out_iff_sip hST
          rcases ho with h0 | h1
          · obtain ⟨_, rfl, rfl, rfl⟩ := h0
            exact Or.inl rfl
          · obtain ⟨_, rfl, rfl, rfl⟩ := h1
            exact Or.inr (rfl)
    · exact absurd rfl hne

theorem S63_step : ∀ (δ : net_label) (N' : Network),
    net_trans S63 δ N' → is_internal_net_label δ → N' = S74 ∨ N' = S75 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S63, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT5_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mClientBOK] (QueueMessage.msg "ClientB" "OK" "unit") = some [] := rfl
          rw [hQe] at hQ
          cases hQ
          exact Or.inl rfl
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mClientBOK] (QueueMessage.msg "ClientB" "Error" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT6_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mProxyRinging] (QueueMessage.msg "Proxy" "Ringing" "unit") = some [] := rfl
          rw [hQe] at hQ
          cases hQ
          exact Or.inr (rfl)
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mProxyRinging] (QueueMessage.msg "Proxy" "Error" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S63, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT5_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT5_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · exact absurd rfl hne

theorem S64_step : ∀ (δ : net_label) (N' : Network),
    net_trans S64 δ N' → is_internal_net_label δ → N' = S76 ∨ N' = S77 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S64, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT5_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mClientBError] (QueueMessage.msg "ClientB" "OK" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mClientBError] (QueueMessage.msg "ClientB" "Error" "unit") = some [] := rfl
          rw [hQe] at hQ
          cases hQ
          exact Or.inl rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT6_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mProxyRinging] (QueueMessage.msg "Proxy" "Ringing" "unit") = some [] := rfl
          rw [hQe] at hQ
          cases hQ
          exact Or.inr (rfl)
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mProxyRinging] (QueueMessage.msg "Proxy" "Error" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S64, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT5_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT5_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · exact absurd rfl hne

theorem S65_step : ∀ (δ : net_label) (N' : Network),
    net_trans S65 δ N' → is_internal_net_label δ → N' = S75 ∨ N' = S78 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S65, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT6_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mProxyRinging] (QueueMessage.msg "Proxy" "Ringing" "unit") = some [] := rfl
          rw [hQe] at hQ
          cases hQ
          exact Or.inl rfl
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mProxyRinging] (QueueMessage.msg "Proxy" "Error" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT5_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mClientBOK] (QueueMessage.msg "ClientB" "OK" "unit") = some [] := rfl
          rw [hQe] at hQ
          cases hQ
          exact Or.inr (rfl)
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mClientBOK] (QueueMessage.msg "ClientB" "Error" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S65, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT5_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT5_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne

theorem S66_step : ∀ (δ : net_label) (N' : Network),
    net_trans S66 δ N' → is_internal_net_label δ → N' = S77 ∨ N' = S79 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S66, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT6_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mProxyRinging] (QueueMessage.msg "Proxy" "Ringing" "unit") = some [] := rfl
          rw [hQe] at hQ
          cases hQ
          exact Or.inl rfl
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mProxyRinging] (QueueMessage.msg "Proxy" "Error" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT5_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mClientBError] (QueueMessage.msg "ClientB" "OK" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mClientBError] (QueueMessage.msg "ClientB" "Error" "unit") = some [] := rfl
          rw [hQe] at hQ
          cases hQ
          exact Or.inr (rfl)
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S66, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT5_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT5_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne

theorem S67_step : ∀ (δ : net_label) (N' : Network),
    net_trans S67 δ N' → is_internal_net_label δ → N' = S80 ∨ N' = S81 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S67, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT8_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mProxyTrying, mProxyRinging] (QueueMessage.msg "Proxy" "Trying" "unit") = some [mProxyRinging] := rfl
          rw [hQe] at hQ
          cases hQ
          exact Or.inr (rfl)
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mProxyTrying, mProxyRinging] (QueueMessage.msg "Proxy" "Error" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S67, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT1_out_iff_sip hST
          obtain ⟨heq, _, _, _⟩ := ho
          exact absurd heq (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT1_out_iff_sip hST
          obtain ⟨_, rfl, rfl, rfl⟩ := ho
          exact Or.inl rfl
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · exact absurd rfl hne

theorem S68_step : ∀ (δ : net_label) (N' : Network),
    net_trans S68 δ N' → is_internal_net_label δ → N' = S82 ∨ N' = S83 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S68, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT8_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mProxyTrying, mProxyRinging] (QueueMessage.msg "Proxy" "Trying" "unit") = some [mProxyRinging] := rfl
          rw [hQe] at hQ
          cases hQ
          exact Or.inr (rfl)
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mProxyTrying, mProxyRinging] (QueueMessage.msg "Proxy" "Error" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S68, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT0_out_iff_sip hST
          obtain ⟨heq, _, _, _⟩ := ho
          exact absurd heq (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT0_out_iff_sip hST
          obtain ⟨_, rfl, rfl, rfl⟩ := ho
          exact Or.inl rfl
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · exact absurd rfl hne

theorem S69_step : ∀ (δ : net_label) (N' : Network),
    net_trans S69 δ N' → is_internal_net_label δ → N' = S80 ∨ N' = S81 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S69, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT8_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mProxyTrying, mProxyRinging] (QueueMessage.msg "Proxy" "Trying" "unit") = some [mProxyRinging] := rfl
          rw [hQe] at hQ
          cases hQ
          exact Or.inr (rfl)
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mProxyTrying, mProxyRinging] (QueueMessage.msg "Proxy" "Error" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S69, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT1_out_iff_sip hST
          obtain ⟨_, rfl, rfl, rfl⟩ := ho
          exact Or.inl rfl
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT1_out_iff_sip hST
          obtain ⟨heq, _, _, _⟩ := ho
          exact absurd heq (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne

theorem S70_step : ∀ (δ : net_label) (N' : Network),
    net_trans S70 δ N' → is_internal_net_label δ → N' = S82 ∨ N' = S83 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S70, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT8_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mProxyTrying, mProxyRinging] (QueueMessage.msg "Proxy" "Trying" "unit") = some [mProxyRinging] := rfl
          rw [hQe] at hQ
          cases hQ
          exact Or.inr (rfl)
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mProxyTrying, mProxyRinging] (QueueMessage.msg "Proxy" "Error" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S70, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT0_out_iff_sip hST
          obtain ⟨_, rfl, rfl, rfl⟩ := ho
          exact Or.inl rfl
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT0_out_iff_sip hST
          obtain ⟨heq, _, _, _⟩ := ho
          exact absurd heq (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne

theorem S71_no_step : ∀ (δ : net_label) (N' : Network),
    net_trans S71 δ N' → is_internal_net_label δ → False := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S71, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S71, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne

theorem S72_step : ∀ (δ : net_label) (N' : Network),
    net_trans S72 δ N' → is_internal_net_label δ → N' = S84 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S72, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT5_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mClientBOK] (QueueMessage.msg "ClientB" "OK" "unit") = some [] := rfl
          rw [hQe] at hQ
          cases hQ
          exact rfl
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mClientBOK] (QueueMessage.msg "ClientB" "Error" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S72, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT5_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT5_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT3_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT3_no_out_sip h)
    · exact absurd rfl hne

theorem S73_step : ∀ (δ : net_label) (N' : Network),
    net_trans S73 δ N' → is_internal_net_label δ → N' = S85 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S73, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT5_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mClientBError] (QueueMessage.msg "ClientB" "OK" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mClientBError] (QueueMessage.msg "ClientB" "Error" "unit") = some [] := rfl
          rw [hQe] at hQ
          cases hQ
          exact rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S73, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT5_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT5_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT3_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT3_no_out_sip h)
    · exact absurd rfl hne

theorem S74_step : ∀ (δ : net_label) (N' : Network),
    net_trans S74 δ N' → is_internal_net_label δ → N' = S86 ∨ N' = S87 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S74, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT6_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mProxyRinging] (QueueMessage.msg "Proxy" "Ringing" "unit") = some [] := rfl
          rw [hQe] at hQ
          cases hQ
          exact Or.inr (rfl)
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mProxyRinging] (QueueMessage.msg "Proxy" "Error" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S74, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT1_out_iff_sip hST
          obtain ⟨heq, _, _, _⟩ := ho
          exact absurd heq (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT1_out_iff_sip hST
          obtain ⟨_, rfl, rfl, rfl⟩ := ho
          exact Or.inl rfl
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · exact absurd rfl hne

theorem S75_step : ∀ (δ : net_label) (N' : Network),
    net_trans S75 δ N' → is_internal_net_label δ → N' = S88 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S75, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT5_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mClientBOK] (QueueMessage.msg "ClientB" "OK" "unit") = some [] := rfl
          rw [hQe] at hQ
          cases hQ
          exact rfl
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mClientBOK] (QueueMessage.msg "ClientB" "Error" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S75, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT3_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT3_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT5_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT5_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne

theorem S76_step : ∀ (δ : net_label) (N' : Network),
    net_trans S76 δ N' → is_internal_net_label δ → N' = S89 ∨ N' = S90 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S76, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT6_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mProxyRinging] (QueueMessage.msg "Proxy" "Ringing" "unit") = some [] := rfl
          rw [hQe] at hQ
          cases hQ
          exact Or.inr (rfl)
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mProxyRinging] (QueueMessage.msg "Proxy" "Error" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S76, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT0_out_iff_sip hST
          obtain ⟨heq, _, _, _⟩ := ho
          exact absurd heq (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT0_out_iff_sip hST
          obtain ⟨_, rfl, rfl, rfl⟩ := ho
          exact Or.inl rfl
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · exact absurd rfl hne

theorem S77_step : ∀ (δ : net_label) (N' : Network),
    net_trans S77 δ N' → is_internal_net_label δ → N' = S91 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S77, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT5_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mClientBError] (QueueMessage.msg "ClientB" "OK" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mClientBError] (QueueMessage.msg "ClientB" "Error" "unit") = some [] := rfl
          rw [hQe] at hQ
          cases hQ
          exact rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S77, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT3_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT3_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT5_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT5_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne

theorem S78_step : ∀ (δ : net_label) (N' : Network),
    net_trans S78 δ N' → is_internal_net_label δ → N' = S86 ∨ N' = S87 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S78, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT6_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mProxyRinging] (QueueMessage.msg "Proxy" "Ringing" "unit") = some [] := rfl
          rw [hQe] at hQ
          cases hQ
          exact Or.inr (rfl)
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mProxyRinging] (QueueMessage.msg "Proxy" "Error" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S78, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT1_out_iff_sip hST
          obtain ⟨_, rfl, rfl, rfl⟩ := ho
          exact Or.inl rfl
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT1_out_iff_sip hST
          obtain ⟨heq, _, _, _⟩ := ho
          exact absurd heq (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne

theorem S79_step : ∀ (δ : net_label) (N' : Network),
    net_trans S79 δ N' → is_internal_net_label δ → N' = S89 ∨ N' = S90 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S79, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT6_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mProxyRinging] (QueueMessage.msg "Proxy" "Ringing" "unit") = some [] := rfl
          rw [hQe] at hQ
          cases hQ
          exact Or.inr (rfl)
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mProxyRinging] (QueueMessage.msg "Proxy" "Error" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S79, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT0_out_iff_sip hST
          obtain ⟨_, rfl, rfl, rfl⟩ := ho
          exact Or.inl rfl
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT0_out_iff_sip hST
          obtain ⟨heq, _, _, _⟩ := ho
          exact absurd heq (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne

theorem S80_step : ∀ (δ : net_label) (N' : Network),
    net_trans S80 δ N' → is_internal_net_label δ → N' = S86 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S80, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT8_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mProxyTrying, mProxyRinging, mProxyOK] (QueueMessage.msg "Proxy" "Trying" "unit") = some [mProxyRinging, mProxyOK] := rfl
          rw [hQe] at hQ
          cases hQ
          exact rfl
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mProxyTrying, mProxyRinging, mProxyOK] (QueueMessage.msg "Proxy" "Error" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S80, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne

theorem S81_step : ∀ (δ : net_label) (N' : Network),
    net_trans S81 δ N' → is_internal_net_label δ → N' = S87 ∨ N' = S86 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S81, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT6_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mProxyRinging] (QueueMessage.msg "Proxy" "Ringing" "unit") = some [] := rfl
          rw [hQe] at hQ
          cases hQ
          exact Or.inl rfl
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mProxyRinging] (QueueMessage.msg "Proxy" "Error" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S81, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT1_out_iff_sip hST
          obtain ⟨_, rfl, rfl, rfl⟩ := ho
          exact Or.inr (rfl)
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT1_out_iff_sip hST
          obtain ⟨heq, _, _, _⟩ := ho
          exact absurd heq (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne

theorem S82_step : ∀ (δ : net_label) (N' : Network),
    net_trans S82 δ N' → is_internal_net_label δ → N' = S89 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S82, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT8_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mProxyTrying, mProxyRinging, mProxyError] (QueueMessage.msg "Proxy" "Trying" "unit") = some [mProxyRinging, mProxyError] := rfl
          rw [hQe] at hQ
          cases hQ
          exact rfl
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mProxyTrying, mProxyRinging, mProxyError] (QueueMessage.msg "Proxy" "Error" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S82, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT8_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne

theorem S83_step : ∀ (δ : net_label) (N' : Network),
    net_trans S83 δ N' → is_internal_net_label δ → N' = S90 ∨ N' = S89 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S83, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT6_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mProxyRinging] (QueueMessage.msg "Proxy" "Ringing" "unit") = some [] := rfl
          rw [hQe] at hQ
          cases hQ
          exact Or.inl rfl
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mProxyRinging] (QueueMessage.msg "Proxy" "Error" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S83, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT0_out_iff_sip hST
          obtain ⟨_, rfl, rfl, rfl⟩ := ho
          exact Or.inr (rfl)
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT0_out_iff_sip hST
          obtain ⟨heq, _, _, _⟩ := ho
          exact absurd heq (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne

theorem S84_step : ∀ (δ : net_label) (N' : Network),
    net_trans S84 δ N' → is_internal_net_label δ → N' = S92 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S84, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S84, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT1_out_iff_sip hST
          obtain ⟨heq, _, _, _⟩ := ho
          exact absurd heq (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT1_out_iff_sip hST
          obtain ⟨_, rfl, rfl, rfl⟩ := ho
          exact rfl
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT3_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT3_no_out_sip h)
    · exact absurd rfl hne

theorem S85_step : ∀ (δ : net_label) (N' : Network),
    net_trans S85 δ N' → is_internal_net_label δ → N' = S93 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S85, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S85, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT0_out_iff_sip hST
          obtain ⟨heq, _, _, _⟩ := ho
          exact absurd heq (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT0_out_iff_sip hST
          obtain ⟨_, rfl, rfl, rfl⟩ := ho
          exact rfl
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT3_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT3_no_out_sip h)
    · exact absurd rfl hne

theorem S86_step : ∀ (δ : net_label) (N' : Network),
    net_trans S86 δ N' → is_internal_net_label δ → N' = S92 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S86, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT6_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mProxyRinging, mProxyOK] (QueueMessage.msg "Proxy" "Ringing" "unit") = some [mProxyOK] := rfl
          rw [hQe] at hQ
          cases hQ
          exact rfl
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mProxyRinging, mProxyOK] (QueueMessage.msg "Proxy" "Error" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S86, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne

theorem S87_step : ∀ (δ : net_label) (N' : Network),
    net_trans S87 δ N' → is_internal_net_label δ → N' = S92 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S87, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S87, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT3_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT3_no_out_sip h)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT1_out_iff_sip hST
          obtain ⟨_, rfl, rfl, rfl⟩ := ho
          exact rfl
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT1_out_iff_sip hST
          obtain ⟨heq, _, _, _⟩ := ho
          exact absurd heq (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne

theorem S88_step : ∀ (δ : net_label) (N' : Network),
    net_trans S88 δ N' → is_internal_net_label δ → N' = S92 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S88, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S88, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT1_out_iff_sip hST
          obtain ⟨_, rfl, rfl, rfl⟩ := ho
          exact rfl
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT1_out_iff_sip hST
          obtain ⟨heq, _, _, _⟩ := ho
          exact absurd heq (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT3_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT3_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne

theorem S89_step : ∀ (δ : net_label) (N' : Network),
    net_trans S89 δ N' → is_internal_net_label δ → N' = S93 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S89, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT6_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mProxyRinging, mProxyError] (QueueMessage.msg "Proxy" "Ringing" "unit") = some [mProxyError] := rfl
          rw [hQe] at hQ
          cases hQ
          exact rfl
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mProxyRinging, mProxyError] (QueueMessage.msg "Proxy" "Error" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S89, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT6_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne

theorem S90_step : ∀ (δ : net_label) (N' : Network),
    net_trans S90 δ N' → is_internal_net_label δ → N' = S93 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S90, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S90, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT3_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT3_no_out_sip h)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT0_out_iff_sip hST
          obtain ⟨_, rfl, rfl, rfl⟩ := ho
          exact rfl
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT0_out_iff_sip hST
          obtain ⟨heq, _, _, _⟩ := ho
          exact absurd heq (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne

theorem S91_step : ∀ (δ : net_label) (N' : Network),
    net_trans S91 δ N' → is_internal_net_label δ → N' = S93 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S91, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S91, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT0_out_iff_sip hST
          obtain ⟨_, rfl, rfl, rfl⟩ := ho
          exact rfl
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := SipT0_out_iff_sip hST
          obtain ⟨heq, _, _, _⟩ := ho
          exact absurd heq (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT3_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT3_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne

theorem S92_step : ∀ (δ : net_label) (N' : Network),
    net_trans S92 δ N' → is_internal_net_label δ → N' = S71 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S92, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT3_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mProxyOK] (QueueMessage.msg "Proxy" "OK" "unit") = some [] := rfl
          rw [hQe] at hQ
          cases hQ
          exact rfl
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mProxyOK] (QueueMessage.msg "Proxy" "Error" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S92, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT3_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT3_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne

theorem S93_step : ∀ (δ : net_label) (N' : Network),
    net_trans S93 δ N' → is_internal_net_label δ → N' = S71 := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [S93, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := SipT3_inp_iff_sip hST
        obtain ⟨rfl, hbr⟩ := hi
        rcases hbr with h0 | h1
        · obtain ⟨_, rfl, rfl, rfl⟩ := h0
          have hQe : Queue.dequeue [mProxyError] (QueueMessage.msg "Proxy" "OK" "unit") = none := rfl
          rw [hQe] at hQ
          cases hQ
        · obtain ⟨_, rfl, rfl, rfl⟩ := h1
          have hQe : Queue.dequeue [mProxyError] (QueueMessage.msg "Proxy" "Error" "unit") = some [] := rfl
          rw [hQe] at hQ
          cases hQ
          exact rfl
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ => simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [S93, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT3_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => SipT3_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_sip h)
    · exact absurd rfl hne

theorem tW0 : net_trans S0 (net_label.τ_comm "ClientA" "Proxy" "INVITE" "unit") S1 := by
  have h_send : sq_trans (SIPClientA, []) (sq_action.send "Proxy" "INVITE" "unit") (SipT8, []) := by
    apply sq_trans.send
    unfold SIPClientA
    apply st_trans.intC
    exact List.mem_cons.mpr (Or.inl rfl)
  have h_recv : sq_trans (SIPProxy, []) (sq_action.recv "ClientA" "INVITE" "unit") (SIPProxy, [] ++ [QueueMessage.msg "ClientA" "INVITE" "unit"]) :=
    sq_trans.recv
  have hmem_p : ("ClientA", (SIPClientA, [])) ∈ S0 := by simp [S0]
  have hmem_q : ("Proxy", (SIPProxy, [])) ∈ S0 := by simp [S0]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q
theorem tW1 : net_trans S1 (net_label.τ_dequeue "Proxy" "ClientA" "INVITE" "unit") S2 := by
  have hSQ : sq_trans (SIPProxy, [mClientAINVITE]) (sq_action.dequeue "ClientA" "INVITE" "unit") (SipT11, []) := by
    apply sq_trans.dequeue
    · unfold SIPProxy
      apply st_trans.extC
      exact List.mem_cons.mpr (Or.inl rfl)
    · rfl
  have hmem : ("Proxy", (SIPProxy, [mClientAINVITE])) ∈ S1 := by simp [S1]
  exact net_trans.dequeue hSQ hmem
theorem tW2 : net_trans S2 (net_label.τ_comm "Proxy" "ClientB" "INVITE" "unit") S3 := by
  have h_send : sq_trans (SipT11, []) (sq_action.send "ClientB" "INVITE" "unit") (SipT10, []) := by
    apply sq_trans.send
    unfold SipT11
    apply st_trans.intC
    exact List.mem_cons.mpr (Or.inl rfl)
  have h_recv : sq_trans (SIPClientB, []) (sq_action.recv "Proxy" "INVITE" "unit") (SIPClientB, [] ++ [QueueMessage.msg "Proxy" "INVITE" "unit"]) :=
    sq_trans.recv
  have hmem_p : ("Proxy", (SipT11, [])) ∈ S2 := by simp [S2]
  have hmem_q : ("ClientB", (SIPClientB, [])) ∈ S2 := by simp [S2]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q
theorem tW3 : net_trans S3 (net_label.τ_dequeue "ClientB" "Proxy" "INVITE" "unit") S5 := by
  have hSQ : sq_trans (SIPClientB, [mProxyINVITE]) (sq_action.dequeue "Proxy" "INVITE" "unit") (SipT4, []) := by
    apply sq_trans.dequeue
    · unfold SIPClientB
      apply st_trans.extC
      exact List.mem_cons.mpr (Or.inl rfl)
    · rfl
  have hmem : ("ClientB", (SIPClientB, [mProxyINVITE])) ∈ S3 := by simp [S3]
  exact net_trans.dequeue hSQ hmem
theorem tW4 : net_trans S4 (net_label.τ_dequeue "ClientA" "Proxy" "Error" "unit") S7 := by
  have hSQ : sq_trans (SipT8, [mProxyError]) (sq_action.dequeue "Proxy" "Error" "unit") (SessionType.tEnd, []) := by
    apply sq_trans.dequeue
    · unfold SipT8
      apply st_trans.extC
      exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
    · rfl
  have hmem : ("ClientA", (SipT8, [mProxyError])) ∈ S4 := by simp [S4]
  exact net_trans.dequeue hSQ hmem
theorem tW5 : net_trans S5 (net_label.τ_comm "ClientB" "Proxy" "Ringing" "unit") S8 := by
  have h_send : sq_trans (SipT4, []) (sq_action.send "Proxy" "Ringing" "unit") (SipT2, []) := by
    apply sq_trans.send
    unfold SipT4
    apply st_trans.intC
    exact List.mem_cons.mpr (Or.inl rfl)
  have h_recv : sq_trans (SipT10, []) (sq_action.recv "ClientB" "Ringing" "unit") (SipT10, [] ++ [QueueMessage.msg "ClientB" "Ringing" "unit"]) :=
    sq_trans.recv
  have hmem_p : ("ClientB", (SipT4, [])) ∈ S5 := by simp [S5]
  have hmem_q : ("Proxy", (SipT10, [])) ∈ S5 := by simp [S5]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q
theorem tW6 : net_trans S6 (net_label.τ_dequeue "ClientA" "Proxy" "Trying" "unit") S11 := by
  have hSQ : sq_trans (SipT8, [mProxyTrying]) (sq_action.dequeue "Proxy" "Trying" "unit") (SipT6, []) := by
    apply sq_trans.dequeue
    · unfold SipT8
      apply st_trans.extC
      exact List.mem_cons.mpr (Or.inl rfl)
    · rfl
  have hmem : ("ClientA", (SipT8, [mProxyTrying])) ∈ S6 := by simp [S6]
  exact net_trans.dequeue hSQ hmem
theorem tW8 : net_trans S8 (net_label.τ_comm "Proxy" "ClientA" "Trying" "unit") S13 := by
  have h_send : sq_trans (SipT10, [mClientBRinging]) (sq_action.send "ClientA" "Trying" "unit") (SipT9, [mClientBRinging]) := by
    apply sq_trans.send
    unfold SipT10
    apply st_trans.intC
    exact List.mem_cons.mpr (Or.inl rfl)
  have h_recv : sq_trans (SipT8, []) (sq_action.recv "Proxy" "Trying" "unit") (SipT8, [] ++ [QueueMessage.msg "Proxy" "Trying" "unit"]) :=
    sq_trans.recv
  have hmem_p : ("Proxy", (SipT10, [mClientBRinging])) ∈ S8 := by simp [S8]
  have hmem_q : ("ClientA", (SipT8, [])) ∈ S8 := by simp [S8]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q
theorem tW9 : net_trans S9 (net_label.τ_comm "Proxy" "ClientA" "Trying" "unit") S16 := by
  have h_send : sq_trans (SipT10, [mClientBError]) (sq_action.send "ClientA" "Trying" "unit") (SipT9, [mClientBError]) := by
    apply sq_trans.send
    unfold SipT10
    apply st_trans.intC
    exact List.mem_cons.mpr (Or.inl rfl)
  have h_recv : sq_trans (SipT8, []) (sq_action.recv "Proxy" "Trying" "unit") (SipT8, [] ++ [QueueMessage.msg "Proxy" "Trying" "unit"]) :=
    sq_trans.recv
  have hmem_p : ("Proxy", (SipT10, [mClientBError])) ∈ S9 := by simp [S9]
  have hmem_q : ("ClientA", (SipT8, [])) ∈ S9 := by simp [S9]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q
theorem tW10 : net_trans S10 (net_label.τ_dequeue "ClientA" "Proxy" "Trying" "unit") S17 := by
  have hSQ : sq_trans (SipT8, [mProxyTrying]) (sq_action.dequeue "Proxy" "Trying" "unit") (SipT6, []) := by
    apply sq_trans.dequeue
    · unfold SipT8
      apply st_trans.extC
      exact List.mem_cons.mpr (Or.inl rfl)
    · rfl
  have hmem : ("ClientA", (SipT8, [mProxyTrying])) ∈ S10 := by simp [S10]
  exact net_trans.dequeue hSQ hmem
theorem tW11 : net_trans S11 (net_label.τ_dequeue "ClientB" "Proxy" "INVITE" "unit") S20 := by
  have hSQ : sq_trans (SIPClientB, [mProxyINVITE]) (sq_action.dequeue "Proxy" "INVITE" "unit") (SipT4, []) := by
    apply sq_trans.dequeue
    · unfold SIPClientB
      apply st_trans.extC
      exact List.mem_cons.mpr (Or.inl rfl)
    · rfl
  have hmem : ("ClientB", (SIPClientB, [mProxyINVITE])) ∈ S11 := by simp [S11]
  exact net_trans.dequeue hSQ hmem
theorem tW12 : net_trans S12 (net_label.τ_comm "ClientB" "Proxy" "Ringing" "unit") S18 := by
  have h_send : sq_trans (SipT4, []) (sq_action.send "Proxy" "Ringing" "unit") (SipT2, []) := by
    apply sq_trans.send
    unfold SipT4
    apply st_trans.intC
    exact List.mem_cons.mpr (Or.inl rfl)
  have h_recv : sq_trans (SipT9, []) (sq_action.recv "ClientB" "Ringing" "unit") (SipT9, [] ++ [QueueMessage.msg "ClientB" "Ringing" "unit"]) :=
    sq_trans.recv
  have hmem_p : ("ClientB", (SipT4, [])) ∈ S12 := by simp [S12]
  have hmem_q : ("Proxy", (SipT9, [])) ∈ S12 := by simp [S12]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q
theorem tW13 : net_trans S13 (net_label.τ_dequeue "ClientA" "Proxy" "Trying" "unit") S22 := by
  have hSQ : sq_trans (SipT8, [mProxyTrying]) (sq_action.dequeue "Proxy" "Trying" "unit") (SipT6, []) := by
    apply sq_trans.dequeue
    · unfold SipT8
      apply st_trans.extC
      exact List.mem_cons.mpr (Or.inl rfl)
    · rfl
  have hmem : ("ClientA", (SipT8, [mProxyTrying])) ∈ S13 := by simp [S13]
  exact net_trans.dequeue hSQ hmem
theorem tW14 : net_trans S14 (net_label.τ_comm "Proxy" "ClientA" "Trying" "unit") S26 := by
  have h_send : sq_trans (SipT10, [mClientBRinging, mClientBOK]) (sq_action.send "ClientA" "Trying" "unit") (SipT9, [mClientBRinging, mClientBOK]) := by
    apply sq_trans.send
    unfold SipT10
    apply st_trans.intC
    exact List.mem_cons.mpr (Or.inl rfl)
  have h_recv : sq_trans (SipT8, []) (sq_action.recv "Proxy" "Trying" "unit") (SipT8, [] ++ [QueueMessage.msg "Proxy" "Trying" "unit"]) :=
    sq_trans.recv
  have hmem_p : ("Proxy", (SipT10, [mClientBRinging, mClientBOK])) ∈ S14 := by simp [S14]
  have hmem_q : ("ClientA", (SipT8, [])) ∈ S14 := by simp [S14]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q
theorem tW15 : net_trans S15 (net_label.τ_comm "Proxy" "ClientA" "Trying" "unit") S27 := by
  have h_send : sq_trans (SipT10, [mClientBRinging, mClientBError]) (sq_action.send "ClientA" "Trying" "unit") (SipT9, [mClientBRinging, mClientBError]) := by
    apply sq_trans.send
    unfold SipT10
    apply st_trans.intC
    exact List.mem_cons.mpr (Or.inl rfl)
  have h_recv : sq_trans (SipT8, []) (sq_action.recv "Proxy" "Trying" "unit") (SipT8, [] ++ [QueueMessage.msg "Proxy" "Trying" "unit"]) :=
    sq_trans.recv
  have hmem_p : ("Proxy", (SipT10, [mClientBRinging, mClientBError])) ∈ S15 := by simp [S15]
  have hmem_q : ("ClientA", (SipT8, [])) ∈ S15 := by simp [S15]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q
theorem tW16 : net_trans S16 (net_label.τ_dequeue "ClientA" "Proxy" "Trying" "unit") S28 := by
  have hSQ : sq_trans (SipT8, [mProxyTrying]) (sq_action.dequeue "Proxy" "Trying" "unit") (SipT6, []) := by
    apply sq_trans.dequeue
    · unfold SipT8
      apply st_trans.extC
      exact List.mem_cons.mpr (Or.inl rfl)
    · rfl
  have hmem : ("ClientA", (SipT8, [mProxyTrying])) ∈ S16 := by simp [S16]
  exact net_trans.dequeue hSQ hmem
theorem tW17 : net_trans S17 (net_label.τ_comm "ClientB" "Proxy" "Ringing" "unit") S30 := by
  have h_send : sq_trans (SipT4, []) (sq_action.send "Proxy" "Ringing" "unit") (SipT2, []) := by
    apply sq_trans.send
    unfold SipT4
    apply st_trans.intC
    exact List.mem_cons.mpr (Or.inl rfl)
  have h_recv : sq_trans (SipT9, []) (sq_action.recv "ClientB" "Ringing" "unit") (SipT9, [] ++ [QueueMessage.msg "ClientB" "Ringing" "unit"]) :=
    sq_trans.recv
  have hmem_p : ("ClientB", (SipT4, [])) ∈ S17 := by simp [S17]
  have hmem_q : ("Proxy", (SipT9, [])) ∈ S17 := by simp [S17]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q
theorem tW18 : net_trans S18 (net_label.τ_dequeue "Proxy" "ClientB" "Ringing" "unit") S32 := by
  have hSQ : sq_trans (SipT9, [mClientBRinging]) (sq_action.dequeue "ClientB" "Ringing" "unit") (SipT7, []) := by
    apply sq_trans.dequeue
    · unfold SipT9
      apply st_trans.extC
      exact List.mem_cons.mpr (Or.inl rfl)
    · rfl
  have hmem : ("Proxy", (SipT9, [mClientBRinging])) ∈ S18 := by simp [S18]
  exact net_trans.dequeue hSQ hmem
theorem tW19 : net_trans S19 (net_label.τ_dequeue "Proxy" "ClientB" "Error" "unit") S33 := by
  have hSQ : sq_trans (SipT9, [mClientBError]) (sq_action.dequeue "ClientB" "Error" "unit") (SipT0, []) := by
    apply sq_trans.dequeue
    · unfold SipT9
      apply st_trans.extC
      exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
    · rfl
  have hmem : ("Proxy", (SipT9, [mClientBError])) ∈ S19 := by simp [S19]
  exact net_trans.dequeue hSQ hmem
theorem tW20 : net_trans S20 (net_label.τ_comm "ClientB" "Proxy" "Ringing" "unit") S30 := by
  have h_send : sq_trans (SipT4, []) (sq_action.send "Proxy" "Ringing" "unit") (SipT2, []) := by
    apply sq_trans.send
    unfold SipT4
    apply st_trans.intC
    exact List.mem_cons.mpr (Or.inl rfl)
  have h_recv : sq_trans (SipT9, []) (sq_action.recv "ClientB" "Ringing" "unit") (SipT9, [] ++ [QueueMessage.msg "ClientB" "Ringing" "unit"]) :=
    sq_trans.recv
  have hmem_p : ("ClientB", (SipT4, [])) ∈ S20 := by simp [S20]
  have hmem_q : ("Proxy", (SipT9, [])) ∈ S20 := by simp [S20]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q
theorem tW21 : net_trans S21 (net_label.τ_comm "ClientB" "Proxy" "Ringing" "unit") S30 := by
  have h_send : sq_trans (SipT4, []) (sq_action.send "Proxy" "Ringing" "unit") (SipT2, []) := by
    apply sq_trans.send
    unfold SipT4
    apply st_trans.intC
    exact List.mem_cons.mpr (Or.inl rfl)
  have h_recv : sq_trans (SipT9, []) (sq_action.recv "ClientB" "Ringing" "unit") (SipT9, [] ++ [QueueMessage.msg "ClientB" "Ringing" "unit"]) :=
    sq_trans.recv
  have hmem_p : ("ClientB", (SipT4, [])) ∈ S21 := by simp [S21]
  have hmem_q : ("Proxy", (SipT9, [])) ∈ S21 := by simp [S21]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q
theorem tW22 : net_trans S22 (net_label.τ_dequeue "Proxy" "ClientB" "Ringing" "unit") S34 := by
  have hSQ : sq_trans (SipT9, [mClientBRinging]) (sq_action.dequeue "ClientB" "Ringing" "unit") (SipT7, []) := by
    apply sq_trans.dequeue
    · unfold SipT9
      apply st_trans.extC
      exact List.mem_cons.mpr (Or.inl rfl)
    · rfl
  have hmem : ("Proxy", (SipT9, [mClientBRinging])) ∈ S22 := by simp [S22]
  exact net_trans.dequeue hSQ hmem
theorem tW23 : net_trans S23 (net_label.τ_comm "Proxy" "ClientA" "Ringing" "unit") S37 := by
  have h_send : sq_trans (SipT7, []) (sq_action.send "ClientA" "Ringing" "unit") (SipT5, []) := by
    apply sq_trans.send
    unfold SipT7
    apply st_trans.intC
    exact List.mem_cons.mpr (Or.inl rfl)
  have h_recv : sq_trans (SipT8, [mProxyTrying]) (sq_action.recv "Proxy" "Ringing" "unit") (SipT8, [mProxyTrying] ++ [QueueMessage.msg "Proxy" "Ringing" "unit"]) :=
    sq_trans.recv
  have hmem_p : ("Proxy", (SipT7, [])) ∈ S23 := by simp [S23]
  have hmem_q : ("ClientA", (SipT8, [mProxyTrying])) ∈ S23 := by simp [S23]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q
theorem tW24 : net_trans S24 (net_label.τ_dequeue "Proxy" "ClientB" "Ringing" "unit") S39 := by
  have hSQ : sq_trans (SipT9, [mClientBRinging, mClientBOK]) (sq_action.dequeue "ClientB" "Ringing" "unit") (SipT7, [mClientBOK]) := by
    apply sq_trans.dequeue
    · unfold SipT9
      apply st_trans.extC
      exact List.mem_cons.mpr (Or.inl rfl)
    · rfl
  have hmem : ("Proxy", (SipT9, [mClientBRinging, mClientBOK])) ∈ S24 := by simp [S24]
  exact net_trans.dequeue hSQ hmem
theorem tW25 : net_trans S25 (net_label.τ_dequeue "Proxy" "ClientB" "Ringing" "unit") S40 := by
  have hSQ : sq_trans (SipT9, [mClientBRinging, mClientBError]) (sq_action.dequeue "ClientB" "Ringing" "unit") (SipT7, [mClientBError]) := by
    apply sq_trans.dequeue
    · unfold SipT9
      apply st_trans.extC
      exact List.mem_cons.mpr (Or.inl rfl)
    · rfl
  have hmem : ("Proxy", (SipT9, [mClientBRinging, mClientBError])) ∈ S25 := by simp [S25]
  exact net_trans.dequeue hSQ hmem
theorem tW26 : net_trans S26 (net_label.τ_dequeue "ClientA" "Proxy" "Trying" "unit") S41 := by
  have hSQ : sq_trans (SipT8, [mProxyTrying]) (sq_action.dequeue "Proxy" "Trying" "unit") (SipT6, []) := by
    apply sq_trans.dequeue
    · unfold SipT8
      apply st_trans.extC
      exact List.mem_cons.mpr (Or.inl rfl)
    · rfl
  have hmem : ("ClientA", (SipT8, [mProxyTrying])) ∈ S26 := by simp [S26]
  exact net_trans.dequeue hSQ hmem
theorem tW27 : net_trans S27 (net_label.τ_dequeue "ClientA" "Proxy" "Trying" "unit") S42 := by
  have hSQ : sq_trans (SipT8, [mProxyTrying]) (sq_action.dequeue "Proxy" "Trying" "unit") (SipT6, []) := by
    apply sq_trans.dequeue
    · unfold SipT8
      apply st_trans.extC
      exact List.mem_cons.mpr (Or.inl rfl)
    · rfl
  have hmem : ("ClientA", (SipT8, [mProxyTrying])) ∈ S27 := by simp [S27]
  exact net_trans.dequeue hSQ hmem
theorem tW28 : net_trans S28 (net_label.τ_dequeue "Proxy" "ClientB" "Error" "unit") S45 := by
  have hSQ : sq_trans (SipT9, [mClientBError]) (sq_action.dequeue "ClientB" "Error" "unit") (SipT0, []) := by
    apply sq_trans.dequeue
    · unfold SipT9
      apply st_trans.extC
      exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
    · rfl
  have hmem : ("Proxy", (SipT9, [mClientBError])) ∈ S28 := by simp [S28]
  exact net_trans.dequeue hSQ hmem
theorem tW29 : net_trans S29 (net_label.τ_comm "Proxy" "ClientA" "Error" "unit") S46 := by
  have h_send : sq_trans (SipT0, []) (sq_action.send "ClientA" "Error" "unit") (SessionType.tEnd, []) := by
    apply sq_trans.send
    unfold SipT0
    apply st_trans.intC
    exact List.mem_cons.mpr (Or.inl rfl)
  have h_recv : sq_trans (SipT8, [mProxyTrying]) (sq_action.recv "Proxy" "Error" "unit") (SipT8, [mProxyTrying] ++ [QueueMessage.msg "Proxy" "Error" "unit"]) :=
    sq_trans.recv
  have hmem_p : ("Proxy", (SipT0, [])) ∈ S29 := by simp [S29]
  have hmem_q : ("ClientA", (SipT8, [mProxyTrying])) ∈ S29 := by simp [S29]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q
theorem tW30 : net_trans S30 (net_label.τ_dequeue "Proxy" "ClientB" "Ringing" "unit") S48 := by
  have hSQ : sq_trans (SipT9, [mClientBRinging]) (sq_action.dequeue "ClientB" "Ringing" "unit") (SipT7, []) := by
    apply sq_trans.dequeue
    · unfold SipT9
      apply st_trans.extC
      exact List.mem_cons.mpr (Or.inl rfl)
    · rfl
  have hmem : ("Proxy", (SipT9, [mClientBRinging])) ∈ S30 := by simp [S30]
  exact net_trans.dequeue hSQ hmem
theorem tW31 : net_trans S31 (net_label.τ_dequeue "Proxy" "ClientB" "Error" "unit") S49 := by
  have hSQ : sq_trans (SipT9, [mClientBError]) (sq_action.dequeue "ClientB" "Error" "unit") (SipT0, []) := by
    apply sq_trans.dequeue
    · unfold SipT9
      apply st_trans.extC
      exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
    · rfl
  have hmem : ("Proxy", (SipT9, [mClientBError])) ∈ S31 := by simp [S31]
  exact net_trans.dequeue hSQ hmem
theorem tW32 : net_trans S32 (net_label.τ_comm "Proxy" "ClientA" "Ringing" "unit") S37 := by
  have h_send : sq_trans (SipT7, []) (sq_action.send "ClientA" "Ringing" "unit") (SipT5, []) := by
    apply sq_trans.send
    unfold SipT7
    apply st_trans.intC
    exact List.mem_cons.mpr (Or.inl rfl)
  have h_recv : sq_trans (SipT8, [mProxyTrying]) (sq_action.recv "Proxy" "Ringing" "unit") (SipT8, [mProxyTrying] ++ [QueueMessage.msg "Proxy" "Ringing" "unit"]) :=
    sq_trans.recv
  have hmem_p : ("Proxy", (SipT7, [])) ∈ S32 := by simp [S32]
  have hmem_q : ("ClientA", (SipT8, [mProxyTrying])) ∈ S32 := by simp [S32]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q
theorem tW33 : net_trans S33 (net_label.τ_comm "Proxy" "ClientA" "Error" "unit") S46 := by
  have h_send : sq_trans (SipT0, []) (sq_action.send "ClientA" "Error" "unit") (SessionType.tEnd, []) := by
    apply sq_trans.send
    unfold SipT0
    apply st_trans.intC
    exact List.mem_cons.mpr (Or.inl rfl)
  have h_recv : sq_trans (SipT8, [mProxyTrying]) (sq_action.recv "Proxy" "Error" "unit") (SipT8, [mProxyTrying] ++ [QueueMessage.msg "Proxy" "Error" "unit"]) :=
    sq_trans.recv
  have hmem_p : ("Proxy", (SipT0, [])) ∈ S33 := by simp [S33]
  have hmem_q : ("ClientA", (SipT8, [mProxyTrying])) ∈ S33 := by simp [S33]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q
theorem tW34 : net_trans S34 (net_label.τ_comm "Proxy" "ClientA" "Ringing" "unit") S50 := by
  have h_send : sq_trans (SipT7, []) (sq_action.send "ClientA" "Ringing" "unit") (SipT5, []) := by
    apply sq_trans.send
    unfold SipT7
    apply st_trans.intC
    exact List.mem_cons.mpr (Or.inl rfl)
  have h_recv : sq_trans (SipT6, []) (sq_action.recv "Proxy" "Ringing" "unit") (SipT6, [] ++ [QueueMessage.msg "Proxy" "Ringing" "unit"]) :=
    sq_trans.recv
  have hmem_p : ("Proxy", (SipT7, [])) ∈ S34 := by simp [S34]
  have hmem_q : ("ClientA", (SipT6, [])) ∈ S34 := by simp [S34]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q
theorem tW35 : net_trans S35 (net_label.τ_dequeue "Proxy" "ClientB" "Ringing" "unit") S51 := by
  have hSQ : sq_trans (SipT9, [mClientBRinging, mClientBOK]) (sq_action.dequeue "ClientB" "Ringing" "unit") (SipT7, [mClientBOK]) := by
    apply sq_trans.dequeue
    · unfold SipT9
      apply st_trans.extC
      exact List.mem_cons.mpr (Or.inl rfl)
    · rfl
  have hmem : ("Proxy", (SipT9, [mClientBRinging, mClientBOK])) ∈ S35 := by simp [S35]
  exact net_trans.dequeue hSQ hmem
theorem tW36 : net_trans S36 (net_label.τ_dequeue "Proxy" "ClientB" "Ringing" "unit") S52 := by
  have hSQ : sq_trans (SipT9, [mClientBRinging, mClientBError]) (sq_action.dequeue "ClientB" "Ringing" "unit") (SipT7, [mClientBError]) := by
    apply sq_trans.dequeue
    · unfold SipT9
      apply st_trans.extC
      exact List.mem_cons.mpr (Or.inl rfl)
    · rfl
  have hmem : ("Proxy", (SipT9, [mClientBRinging, mClientBError])) ∈ S36 := by simp [S36]
  exact net_trans.dequeue hSQ hmem
theorem tW37 : net_trans S37 (net_label.τ_dequeue "ClientA" "Proxy" "Trying" "unit") S50 := by
  have hSQ : sq_trans (SipT8, [mProxyTrying, mProxyRinging]) (sq_action.dequeue "Proxy" "Trying" "unit") (SipT6, [mProxyRinging]) := by
    apply sq_trans.dequeue
    · unfold SipT8
      apply st_trans.extC
      exact List.mem_cons.mpr (Or.inl rfl)
    · rfl
  have hmem : ("ClientA", (SipT8, [mProxyTrying, mProxyRinging])) ∈ S37 := by simp [S37]
  exact net_trans.dequeue hSQ hmem
theorem tW38 : net_trans S38 (net_label.τ_comm "Proxy" "ClientA" "Ringing" "unit") S50 := by
  have h_send : sq_trans (SipT7, []) (sq_action.send "ClientA" "Ringing" "unit") (SipT5, []) := by
    apply sq_trans.send
    unfold SipT7
    apply st_trans.intC
    exact List.mem_cons.mpr (Or.inl rfl)
  have h_recv : sq_trans (SipT6, []) (sq_action.recv "Proxy" "Ringing" "unit") (SipT6, [] ++ [QueueMessage.msg "Proxy" "Ringing" "unit"]) :=
    sq_trans.recv
  have hmem_p : ("Proxy", (SipT7, [])) ∈ S38 := by simp [S38]
  have hmem_q : ("ClientA", (SipT6, [])) ∈ S38 := by simp [S38]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q
theorem tW39 : net_trans S39 (net_label.τ_comm "Proxy" "ClientA" "Ringing" "unit") S55 := by
  have h_send : sq_trans (SipT7, [mClientBOK]) (sq_action.send "ClientA" "Ringing" "unit") (SipT5, [mClientBOK]) := by
    apply sq_trans.send
    unfold SipT7
    apply st_trans.intC
    exact List.mem_cons.mpr (Or.inl rfl)
  have h_recv : sq_trans (SipT8, [mProxyTrying]) (sq_action.recv "Proxy" "Ringing" "unit") (SipT8, [mProxyTrying] ++ [QueueMessage.msg "Proxy" "Ringing" "unit"]) :=
    sq_trans.recv
  have hmem_p : ("Proxy", (SipT7, [mClientBOK])) ∈ S39 := by simp [S39]
  have hmem_q : ("ClientA", (SipT8, [mProxyTrying])) ∈ S39 := by simp [S39]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q
theorem tW40 : net_trans S40 (net_label.τ_comm "Proxy" "ClientA" "Ringing" "unit") S57 := by
  have h_send : sq_trans (SipT7, [mClientBError]) (sq_action.send "ClientA" "Ringing" "unit") (SipT5, [mClientBError]) := by
    apply sq_trans.send
    unfold SipT7
    apply st_trans.intC
    exact List.mem_cons.mpr (Or.inl rfl)
  have h_recv : sq_trans (SipT8, [mProxyTrying]) (sq_action.recv "Proxy" "Ringing" "unit") (SipT8, [mProxyTrying] ++ [QueueMessage.msg "Proxy" "Ringing" "unit"]) :=
    sq_trans.recv
  have hmem_p : ("Proxy", (SipT7, [mClientBError])) ∈ S40 := by simp [S40]
  have hmem_q : ("ClientA", (SipT8, [mProxyTrying])) ∈ S40 := by simp [S40]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q
theorem tW41 : net_trans S41 (net_label.τ_dequeue "Proxy" "ClientB" "Ringing" "unit") S59 := by
  have hSQ : sq_trans (SipT9, [mClientBRinging, mClientBOK]) (sq_action.dequeue "ClientB" "Ringing" "unit") (SipT7, [mClientBOK]) := by
    apply sq_trans.dequeue
    · unfold SipT9
      apply st_trans.extC
      exact List.mem_cons.mpr (Or.inl rfl)
    · rfl
  have hmem : ("Proxy", (SipT9, [mClientBRinging, mClientBOK])) ∈ S41 := by simp [S41]
  exact net_trans.dequeue hSQ hmem
theorem tW42 : net_trans S42 (net_label.τ_dequeue "Proxy" "ClientB" "Ringing" "unit") S60 := by
  have hSQ : sq_trans (SipT9, [mClientBRinging, mClientBError]) (sq_action.dequeue "ClientB" "Ringing" "unit") (SipT7, [mClientBError]) := by
    apply sq_trans.dequeue
    · unfold SipT9
      apply st_trans.extC
      exact List.mem_cons.mpr (Or.inl rfl)
    · rfl
  have hmem : ("Proxy", (SipT9, [mClientBRinging, mClientBError])) ∈ S42 := by simp [S42]
  exact net_trans.dequeue hSQ hmem
theorem tW43 : net_trans S43 (net_label.τ_comm "Proxy" "ClientA" "Ringing" "unit") S55 := by
  have h_send : sq_trans (SipT7, [mClientBOK]) (sq_action.send "ClientA" "Ringing" "unit") (SipT5, [mClientBOK]) := by
    apply sq_trans.send
    unfold SipT7
    apply st_trans.intC
    exact List.mem_cons.mpr (Or.inl rfl)
  have h_recv : sq_trans (SipT8, [mProxyTrying]) (sq_action.recv "Proxy" "Ringing" "unit") (SipT8, [mProxyTrying] ++ [QueueMessage.msg "Proxy" "Ringing" "unit"]) :=
    sq_trans.recv
  have hmem_p : ("Proxy", (SipT7, [mClientBOK])) ∈ S43 := by simp [S43]
  have hmem_q : ("ClientA", (SipT8, [mProxyTrying])) ∈ S43 := by simp [S43]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q
theorem tW44 : net_trans S44 (net_label.τ_comm "Proxy" "ClientA" "Ringing" "unit") S57 := by
  have h_send : sq_trans (SipT7, [mClientBError]) (sq_action.send "ClientA" "Ringing" "unit") (SipT5, [mClientBError]) := by
    apply sq_trans.send
    unfold SipT7
    apply st_trans.intC
    exact List.mem_cons.mpr (Or.inl rfl)
  have h_recv : sq_trans (SipT8, [mProxyTrying]) (sq_action.recv "Proxy" "Ringing" "unit") (SipT8, [mProxyTrying] ++ [QueueMessage.msg "Proxy" "Ringing" "unit"]) :=
    sq_trans.recv
  have hmem_p : ("Proxy", (SipT7, [mClientBError])) ∈ S44 := by simp [S44]
  have hmem_q : ("ClientA", (SipT8, [mProxyTrying])) ∈ S44 := by simp [S44]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q
theorem tW45 : net_trans S45 (net_label.τ_comm "Proxy" "ClientA" "Error" "unit") S61 := by
  have h_send : sq_trans (SipT0, []) (sq_action.send "ClientA" "Error" "unit") (SessionType.tEnd, []) := by
    apply sq_trans.send
    unfold SipT0
    apply st_trans.intC
    exact List.mem_cons.mpr (Or.inl rfl)
  have h_recv : sq_trans (SipT6, []) (sq_action.recv "Proxy" "Error" "unit") (SipT6, [] ++ [QueueMessage.msg "Proxy" "Error" "unit"]) :=
    sq_trans.recv
  have hmem_p : ("Proxy", (SipT0, [])) ∈ S45 := by simp [S45]
  have hmem_q : ("ClientA", (SipT6, [])) ∈ S45 := by simp [S45]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q
theorem tW46 : net_trans S46 (net_label.τ_dequeue "ClientA" "Proxy" "Trying" "unit") S61 := by
  have hSQ : sq_trans (SipT8, [mProxyTrying, mProxyError]) (sq_action.dequeue "Proxy" "Trying" "unit") (SipT6, [mProxyError]) := by
    apply sq_trans.dequeue
    · unfold SipT8
      apply st_trans.extC
      exact List.mem_cons.mpr (Or.inl rfl)
    · rfl
  have hmem : ("ClientA", (SipT8, [mProxyTrying, mProxyError])) ∈ S46 := by simp [S46]
  exact net_trans.dequeue hSQ hmem
theorem tW47 : net_trans S47 (net_label.τ_comm "Proxy" "ClientA" "Error" "unit") S61 := by
  have h_send : sq_trans (SipT0, []) (sq_action.send "ClientA" "Error" "unit") (SessionType.tEnd, []) := by
    apply sq_trans.send
    unfold SipT0
    apply st_trans.intC
    exact List.mem_cons.mpr (Or.inl rfl)
  have h_recv : sq_trans (SipT6, []) (sq_action.recv "Proxy" "Error" "unit") (SipT6, [] ++ [QueueMessage.msg "Proxy" "Error" "unit"]) :=
    sq_trans.recv
  have hmem_p : ("Proxy", (SipT0, [])) ∈ S47 := by simp [S47]
  have hmem_q : ("ClientA", (SipT6, [])) ∈ S47 := by simp [S47]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q
theorem tW48 : net_trans S48 (net_label.τ_comm "Proxy" "ClientA" "Ringing" "unit") S50 := by
  have h_send : sq_trans (SipT7, []) (sq_action.send "ClientA" "Ringing" "unit") (SipT5, []) := by
    apply sq_trans.send
    unfold SipT7
    apply st_trans.intC
    exact List.mem_cons.mpr (Or.inl rfl)
  have h_recv : sq_trans (SipT6, []) (sq_action.recv "Proxy" "Ringing" "unit") (SipT6, [] ++ [QueueMessage.msg "Proxy" "Ringing" "unit"]) :=
    sq_trans.recv
  have hmem_p : ("Proxy", (SipT7, [])) ∈ S48 := by simp [S48]
  have hmem_q : ("ClientA", (SipT6, [])) ∈ S48 := by simp [S48]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q
theorem tW49 : net_trans S49 (net_label.τ_comm "Proxy" "ClientA" "Error" "unit") S61 := by
  have h_send : sq_trans (SipT0, []) (sq_action.send "ClientA" "Error" "unit") (SessionType.tEnd, []) := by
    apply sq_trans.send
    unfold SipT0
    apply st_trans.intC
    exact List.mem_cons.mpr (Or.inl rfl)
  have h_recv : sq_trans (SipT6, []) (sq_action.recv "Proxy" "Error" "unit") (SipT6, [] ++ [QueueMessage.msg "Proxy" "Error" "unit"]) :=
    sq_trans.recv
  have hmem_p : ("Proxy", (SipT0, [])) ∈ S49 := by simp [S49]
  have hmem_q : ("ClientA", (SipT6, [])) ∈ S49 := by simp [S49]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q
theorem tW50 : net_trans S50 (net_label.τ_dequeue "ClientA" "Proxy" "Ringing" "unit") S62 := by
  have hSQ : sq_trans (SipT6, [mProxyRinging]) (sq_action.dequeue "Proxy" "Ringing" "unit") (SipT3, []) := by
    apply sq_trans.dequeue
    · unfold SipT6
      apply st_trans.extC
      exact List.mem_cons.mpr (Or.inl rfl)
    · rfl
  have hmem : ("ClientA", (SipT6, [mProxyRinging])) ∈ S50 := by simp [S50]
  exact net_trans.dequeue hSQ hmem
theorem tW51 : net_trans S51 (net_label.τ_comm "Proxy" "ClientA" "Ringing" "unit") S65 := by
  have h_send : sq_trans (SipT7, [mClientBOK]) (sq_action.send "ClientA" "Ringing" "unit") (SipT5, [mClientBOK]) := by
    apply sq_trans.send
    unfold SipT7
    apply st_trans.intC
    exact List.mem_cons.mpr (Or.inl rfl)
  have h_recv : sq_trans (SipT6, []) (sq_action.recv "Proxy" "Ringing" "unit") (SipT6, [] ++ [QueueMessage.msg "Proxy" "Ringing" "unit"]) :=
    sq_trans.recv
  have hmem_p : ("Proxy", (SipT7, [mClientBOK])) ∈ S51 := by simp [S51]
  have hmem_q : ("ClientA", (SipT6, [])) ∈ S51 := by simp [S51]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q
theorem tW52 : net_trans S52 (net_label.τ_comm "Proxy" "ClientA" "Ringing" "unit") S66 := by
  have h_send : sq_trans (SipT7, [mClientBError]) (sq_action.send "ClientA" "Ringing" "unit") (SipT5, [mClientBError]) := by
    apply sq_trans.send
    unfold SipT7
    apply st_trans.intC
    exact List.mem_cons.mpr (Or.inl rfl)
  have h_recv : sq_trans (SipT6, []) (sq_action.recv "Proxy" "Ringing" "unit") (SipT6, [] ++ [QueueMessage.msg "Proxy" "Ringing" "unit"]) :=
    sq_trans.recv
  have hmem_p : ("Proxy", (SipT7, [mClientBError])) ∈ S52 := by simp [S52]
  have hmem_q : ("ClientA", (SipT6, [])) ∈ S52 := by simp [S52]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q
theorem tW53 : net_trans S53 (net_label.τ_dequeue "Proxy" "ClientB" "OK" "unit") S67 := by
  have hSQ : sq_trans (SipT5, [mClientBOK]) (sq_action.dequeue "ClientB" "OK" "unit") (SipT1, []) := by
    apply sq_trans.dequeue
    · unfold SipT5
      apply st_trans.extC
      exact List.mem_cons.mpr (Or.inl rfl)
    · rfl
  have hmem : ("Proxy", (SipT5, [mClientBOK])) ∈ S53 := by simp [S53]
  exact net_trans.dequeue hSQ hmem
theorem tW54 : net_trans S54 (net_label.τ_dequeue "Proxy" "ClientB" "Error" "unit") S68 := by
  have hSQ : sq_trans (SipT5, [mClientBError]) (sq_action.dequeue "ClientB" "Error" "unit") (SipT0, []) := by
    apply sq_trans.dequeue
    · unfold SipT5
      apply st_trans.extC
      exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
    · rfl
  have hmem : ("Proxy", (SipT5, [mClientBError])) ∈ S54 := by simp [S54]
  exact net_trans.dequeue hSQ hmem
theorem tW55 : net_trans S55 (net_label.τ_dequeue "ClientA" "Proxy" "Trying" "unit") S65 := by
  have hSQ : sq_trans (SipT8, [mProxyTrying, mProxyRinging]) (sq_action.dequeue "Proxy" "Trying" "unit") (SipT6, [mProxyRinging]) := by
    apply sq_trans.dequeue
    · unfold SipT8
      apply st_trans.extC
      exact List.mem_cons.mpr (Or.inl rfl)
    · rfl
  have hmem : ("ClientA", (SipT8, [mProxyTrying, mProxyRinging])) ∈ S55 := by simp [S55]
  exact net_trans.dequeue hSQ hmem
theorem tW56 : net_trans S56 (net_label.τ_comm "Proxy" "ClientA" "Ringing" "unit") S65 := by
  have h_send : sq_trans (SipT7, [mClientBOK]) (sq_action.send "ClientA" "Ringing" "unit") (SipT5, [mClientBOK]) := by
    apply sq_trans.send
    unfold SipT7
    apply st_trans.intC
    exact List.mem_cons.mpr (Or.inl rfl)
  have h_recv : sq_trans (SipT6, []) (sq_action.recv "Proxy" "Ringing" "unit") (SipT6, [] ++ [QueueMessage.msg "Proxy" "Ringing" "unit"]) :=
    sq_trans.recv
  have hmem_p : ("Proxy", (SipT7, [mClientBOK])) ∈ S56 := by simp [S56]
  have hmem_q : ("ClientA", (SipT6, [])) ∈ S56 := by simp [S56]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q
theorem tW57 : net_trans S57 (net_label.τ_dequeue "ClientA" "Proxy" "Trying" "unit") S66 := by
  have hSQ : sq_trans (SipT8, [mProxyTrying, mProxyRinging]) (sq_action.dequeue "Proxy" "Trying" "unit") (SipT6, [mProxyRinging]) := by
    apply sq_trans.dequeue
    · unfold SipT8
      apply st_trans.extC
      exact List.mem_cons.mpr (Or.inl rfl)
    · rfl
  have hmem : ("ClientA", (SipT8, [mProxyTrying, mProxyRinging])) ∈ S57 := by simp [S57]
  exact net_trans.dequeue hSQ hmem
theorem tW58 : net_trans S58 (net_label.τ_comm "Proxy" "ClientA" "Ringing" "unit") S66 := by
  have h_send : sq_trans (SipT7, [mClientBError]) (sq_action.send "ClientA" "Ringing" "unit") (SipT5, [mClientBError]) := by
    apply sq_trans.send
    unfold SipT7
    apply st_trans.intC
    exact List.mem_cons.mpr (Or.inl rfl)
  have h_recv : sq_trans (SipT6, []) (sq_action.recv "Proxy" "Ringing" "unit") (SipT6, [] ++ [QueueMessage.msg "Proxy" "Ringing" "unit"]) :=
    sq_trans.recv
  have hmem_p : ("Proxy", (SipT7, [mClientBError])) ∈ S58 := by simp [S58]
  have hmem_q : ("ClientA", (SipT6, [])) ∈ S58 := by simp [S58]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q
theorem tW59 : net_trans S59 (net_label.τ_comm "Proxy" "ClientA" "Ringing" "unit") S65 := by
  have h_send : sq_trans (SipT7, [mClientBOK]) (sq_action.send "ClientA" "Ringing" "unit") (SipT5, [mClientBOK]) := by
    apply sq_trans.send
    unfold SipT7
    apply st_trans.intC
    exact List.mem_cons.mpr (Or.inl rfl)
  have h_recv : sq_trans (SipT6, []) (sq_action.recv "Proxy" "Ringing" "unit") (SipT6, [] ++ [QueueMessage.msg "Proxy" "Ringing" "unit"]) :=
    sq_trans.recv
  have hmem_p : ("Proxy", (SipT7, [mClientBOK])) ∈ S59 := by simp [S59]
  have hmem_q : ("ClientA", (SipT6, [])) ∈ S59 := by simp [S59]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q
theorem tW60 : net_trans S60 (net_label.τ_comm "Proxy" "ClientA" "Ringing" "unit") S66 := by
  have h_send : sq_trans (SipT7, [mClientBError]) (sq_action.send "ClientA" "Ringing" "unit") (SipT5, [mClientBError]) := by
    apply sq_trans.send
    unfold SipT7
    apply st_trans.intC
    exact List.mem_cons.mpr (Or.inl rfl)
  have h_recv : sq_trans (SipT6, []) (sq_action.recv "Proxy" "Ringing" "unit") (SipT6, [] ++ [QueueMessage.msg "Proxy" "Ringing" "unit"]) :=
    sq_trans.recv
  have hmem_p : ("Proxy", (SipT7, [mClientBError])) ∈ S60 := by simp [S60]
  have hmem_q : ("ClientA", (SipT6, [])) ∈ S60 := by simp [S60]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q
theorem tW61 : net_trans S61 (net_label.τ_dequeue "ClientA" "Proxy" "Error" "unit") S71 := by
  have hSQ : sq_trans (SipT6, [mProxyError]) (sq_action.dequeue "Proxy" "Error" "unit") (SessionType.tEnd, []) := by
    apply sq_trans.dequeue
    · unfold SipT6
      apply st_trans.extC
      exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
    · rfl
  have hmem : ("ClientA", (SipT6, [mProxyError])) ∈ S61 := by simp [S61]
  exact net_trans.dequeue hSQ hmem
theorem tW62 : net_trans S62 (net_label.τ_comm "ClientB" "Proxy" "OK" "unit") S72 := by
  have h_send : sq_trans (SipT2, []) (sq_action.send "Proxy" "OK" "unit") (SessionType.tEnd, []) := by
    apply sq_trans.send
    unfold SipT2
    apply st_trans.intC
    exact List.mem_cons.mpr (Or.inl rfl)
  have h_recv : sq_trans (SipT5, []) (sq_action.recv "ClientB" "OK" "unit") (SipT5, [] ++ [QueueMessage.msg "ClientB" "OK" "unit"]) :=
    sq_trans.recv
  have hmem_p : ("ClientB", (SipT2, [])) ∈ S62 := by simp [S62]
  have hmem_q : ("Proxy", (SipT5, [])) ∈ S62 := by simp [S62]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q
theorem tW63 : net_trans S63 (net_label.τ_dequeue "Proxy" "ClientB" "OK" "unit") S74 := by
  have hSQ : sq_trans (SipT5, [mClientBOK]) (sq_action.dequeue "ClientB" "OK" "unit") (SipT1, []) := by
    apply sq_trans.dequeue
    · unfold SipT5
      apply st_trans.extC
      exact List.mem_cons.mpr (Or.inl rfl)
    · rfl
  have hmem : ("Proxy", (SipT5, [mClientBOK])) ∈ S63 := by simp [S63]
  exact net_trans.dequeue hSQ hmem
theorem tW64 : net_trans S64 (net_label.τ_dequeue "Proxy" "ClientB" "Error" "unit") S76 := by
  have hSQ : sq_trans (SipT5, [mClientBError]) (sq_action.dequeue "ClientB" "Error" "unit") (SipT0, []) := by
    apply sq_trans.dequeue
    · unfold SipT5
      apply st_trans.extC
      exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
    · rfl
  have hmem : ("Proxy", (SipT5, [mClientBError])) ∈ S64 := by simp [S64]
  exact net_trans.dequeue hSQ hmem
theorem tW65 : net_trans S65 (net_label.τ_dequeue "ClientA" "Proxy" "Ringing" "unit") S75 := by
  have hSQ : sq_trans (SipT6, [mProxyRinging]) (sq_action.dequeue "Proxy" "Ringing" "unit") (SipT3, []) := by
    apply sq_trans.dequeue
    · unfold SipT6
      apply st_trans.extC
      exact List.mem_cons.mpr (Or.inl rfl)
    · rfl
  have hmem : ("ClientA", (SipT6, [mProxyRinging])) ∈ S65 := by simp [S65]
  exact net_trans.dequeue hSQ hmem
theorem tW66 : net_trans S66 (net_label.τ_dequeue "ClientA" "Proxy" "Ringing" "unit") S77 := by
  have hSQ : sq_trans (SipT6, [mProxyRinging]) (sq_action.dequeue "Proxy" "Ringing" "unit") (SipT3, []) := by
    apply sq_trans.dequeue
    · unfold SipT6
      apply st_trans.extC
      exact List.mem_cons.mpr (Or.inl rfl)
    · rfl
  have hmem : ("ClientA", (SipT6, [mProxyRinging])) ∈ S66 := by simp [S66]
  exact net_trans.dequeue hSQ hmem
theorem tW67 : net_trans S67 (net_label.τ_comm "Proxy" "ClientA" "OK" "unit") S80 := by
  have h_send : sq_trans (SipT1, []) (sq_action.send "ClientA" "OK" "unit") (SessionType.tEnd, []) := by
    apply sq_trans.send
    unfold SipT1
    apply st_trans.intC
    exact List.mem_cons.mpr (Or.inl rfl)
  have h_recv : sq_trans (SipT8, [mProxyTrying, mProxyRinging]) (sq_action.recv "Proxy" "OK" "unit") (SipT8, [mProxyTrying, mProxyRinging] ++ [QueueMessage.msg "Proxy" "OK" "unit"]) :=
    sq_trans.recv
  have hmem_p : ("Proxy", (SipT1, [])) ∈ S67 := by simp [S67]
  have hmem_q : ("ClientA", (SipT8, [mProxyTrying, mProxyRinging])) ∈ S67 := by simp [S67]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q
theorem tW68 : net_trans S68 (net_label.τ_comm "Proxy" "ClientA" "Error" "unit") S82 := by
  have h_send : sq_trans (SipT0, []) (sq_action.send "ClientA" "Error" "unit") (SessionType.tEnd, []) := by
    apply sq_trans.send
    unfold SipT0
    apply st_trans.intC
    exact List.mem_cons.mpr (Or.inl rfl)
  have h_recv : sq_trans (SipT8, [mProxyTrying, mProxyRinging]) (sq_action.recv "Proxy" "Error" "unit") (SipT8, [mProxyTrying, mProxyRinging] ++ [QueueMessage.msg "Proxy" "Error" "unit"]) :=
    sq_trans.recv
  have hmem_p : ("Proxy", (SipT0, [])) ∈ S68 := by simp [S68]
  have hmem_q : ("ClientA", (SipT8, [mProxyTrying, mProxyRinging])) ∈ S68 := by simp [S68]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q
theorem tW69 : net_trans S69 (net_label.τ_comm "Proxy" "ClientA" "OK" "unit") S80 := by
  have h_send : sq_trans (SipT1, []) (sq_action.send "ClientA" "OK" "unit") (SessionType.tEnd, []) := by
    apply sq_trans.send
    unfold SipT1
    apply st_trans.intC
    exact List.mem_cons.mpr (Or.inl rfl)
  have h_recv : sq_trans (SipT8, [mProxyTrying, mProxyRinging]) (sq_action.recv "Proxy" "OK" "unit") (SipT8, [mProxyTrying, mProxyRinging] ++ [QueueMessage.msg "Proxy" "OK" "unit"]) :=
    sq_trans.recv
  have hmem_p : ("Proxy", (SipT1, [])) ∈ S69 := by simp [S69]
  have hmem_q : ("ClientA", (SipT8, [mProxyTrying, mProxyRinging])) ∈ S69 := by simp [S69]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q
theorem tW70 : net_trans S70 (net_label.τ_comm "Proxy" "ClientA" "Error" "unit") S82 := by
  have h_send : sq_trans (SipT0, []) (sq_action.send "ClientA" "Error" "unit") (SessionType.tEnd, []) := by
    apply sq_trans.send
    unfold SipT0
    apply st_trans.intC
    exact List.mem_cons.mpr (Or.inl rfl)
  have h_recv : sq_trans (SipT8, [mProxyTrying, mProxyRinging]) (sq_action.recv "Proxy" "Error" "unit") (SipT8, [mProxyTrying, mProxyRinging] ++ [QueueMessage.msg "Proxy" "Error" "unit"]) :=
    sq_trans.recv
  have hmem_p : ("Proxy", (SipT0, [])) ∈ S70 := by simp [S70]
  have hmem_q : ("ClientA", (SipT8, [mProxyTrying, mProxyRinging])) ∈ S70 := by simp [S70]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q
theorem tW72 : net_trans S72 (net_label.τ_dequeue "Proxy" "ClientB" "OK" "unit") S84 := by
  have hSQ : sq_trans (SipT5, [mClientBOK]) (sq_action.dequeue "ClientB" "OK" "unit") (SipT1, []) := by
    apply sq_trans.dequeue
    · unfold SipT5
      apply st_trans.extC
      exact List.mem_cons.mpr (Or.inl rfl)
    · rfl
  have hmem : ("Proxy", (SipT5, [mClientBOK])) ∈ S72 := by simp [S72]
  exact net_trans.dequeue hSQ hmem
theorem tW73 : net_trans S73 (net_label.τ_dequeue "Proxy" "ClientB" "Error" "unit") S85 := by
  have hSQ : sq_trans (SipT5, [mClientBError]) (sq_action.dequeue "ClientB" "Error" "unit") (SipT0, []) := by
    apply sq_trans.dequeue
    · unfold SipT5
      apply st_trans.extC
      exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
    · rfl
  have hmem : ("Proxy", (SipT5, [mClientBError])) ∈ S73 := by simp [S73]
  exact net_trans.dequeue hSQ hmem
theorem tW74 : net_trans S74 (net_label.τ_comm "Proxy" "ClientA" "OK" "unit") S86 := by
  have h_send : sq_trans (SipT1, []) (sq_action.send "ClientA" "OK" "unit") (SessionType.tEnd, []) := by
    apply sq_trans.send
    unfold SipT1
    apply st_trans.intC
    exact List.mem_cons.mpr (Or.inl rfl)
  have h_recv : sq_trans (SipT6, [mProxyRinging]) (sq_action.recv "Proxy" "OK" "unit") (SipT6, [mProxyRinging] ++ [QueueMessage.msg "Proxy" "OK" "unit"]) :=
    sq_trans.recv
  have hmem_p : ("Proxy", (SipT1, [])) ∈ S74 := by simp [S74]
  have hmem_q : ("ClientA", (SipT6, [mProxyRinging])) ∈ S74 := by simp [S74]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q
theorem tW75 : net_trans S75 (net_label.τ_dequeue "Proxy" "ClientB" "OK" "unit") S88 := by
  have hSQ : sq_trans (SipT5, [mClientBOK]) (sq_action.dequeue "ClientB" "OK" "unit") (SipT1, []) := by
    apply sq_trans.dequeue
    · unfold SipT5
      apply st_trans.extC
      exact List.mem_cons.mpr (Or.inl rfl)
    · rfl
  have hmem : ("Proxy", (SipT5, [mClientBOK])) ∈ S75 := by simp [S75]
  exact net_trans.dequeue hSQ hmem
theorem tW76 : net_trans S76 (net_label.τ_comm "Proxy" "ClientA" "Error" "unit") S89 := by
  have h_send : sq_trans (SipT0, []) (sq_action.send "ClientA" "Error" "unit") (SessionType.tEnd, []) := by
    apply sq_trans.send
    unfold SipT0
    apply st_trans.intC
    exact List.mem_cons.mpr (Or.inl rfl)
  have h_recv : sq_trans (SipT6, [mProxyRinging]) (sq_action.recv "Proxy" "Error" "unit") (SipT6, [mProxyRinging] ++ [QueueMessage.msg "Proxy" "Error" "unit"]) :=
    sq_trans.recv
  have hmem_p : ("Proxy", (SipT0, [])) ∈ S76 := by simp [S76]
  have hmem_q : ("ClientA", (SipT6, [mProxyRinging])) ∈ S76 := by simp [S76]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q
theorem tW77 : net_trans S77 (net_label.τ_dequeue "Proxy" "ClientB" "Error" "unit") S91 := by
  have hSQ : sq_trans (SipT5, [mClientBError]) (sq_action.dequeue "ClientB" "Error" "unit") (SipT0, []) := by
    apply sq_trans.dequeue
    · unfold SipT5
      apply st_trans.extC
      exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
    · rfl
  have hmem : ("Proxy", (SipT5, [mClientBError])) ∈ S77 := by simp [S77]
  exact net_trans.dequeue hSQ hmem
theorem tW78 : net_trans S78 (net_label.τ_comm "Proxy" "ClientA" "OK" "unit") S86 := by
  have h_send : sq_trans (SipT1, []) (sq_action.send "ClientA" "OK" "unit") (SessionType.tEnd, []) := by
    apply sq_trans.send
    unfold SipT1
    apply st_trans.intC
    exact List.mem_cons.mpr (Or.inl rfl)
  have h_recv : sq_trans (SipT6, [mProxyRinging]) (sq_action.recv "Proxy" "OK" "unit") (SipT6, [mProxyRinging] ++ [QueueMessage.msg "Proxy" "OK" "unit"]) :=
    sq_trans.recv
  have hmem_p : ("Proxy", (SipT1, [])) ∈ S78 := by simp [S78]
  have hmem_q : ("ClientA", (SipT6, [mProxyRinging])) ∈ S78 := by simp [S78]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q
theorem tW79 : net_trans S79 (net_label.τ_comm "Proxy" "ClientA" "Error" "unit") S89 := by
  have h_send : sq_trans (SipT0, []) (sq_action.send "ClientA" "Error" "unit") (SessionType.tEnd, []) := by
    apply sq_trans.send
    unfold SipT0
    apply st_trans.intC
    exact List.mem_cons.mpr (Or.inl rfl)
  have h_recv : sq_trans (SipT6, [mProxyRinging]) (sq_action.recv "Proxy" "Error" "unit") (SipT6, [mProxyRinging] ++ [QueueMessage.msg "Proxy" "Error" "unit"]) :=
    sq_trans.recv
  have hmem_p : ("Proxy", (SipT0, [])) ∈ S79 := by simp [S79]
  have hmem_q : ("ClientA", (SipT6, [mProxyRinging])) ∈ S79 := by simp [S79]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q
theorem tW80 : net_trans S80 (net_label.τ_dequeue "ClientA" "Proxy" "Trying" "unit") S86 := by
  have hSQ : sq_trans (SipT8, [mProxyTrying, mProxyRinging, mProxyOK]) (sq_action.dequeue "Proxy" "Trying" "unit") (SipT6, [mProxyRinging, mProxyOK]) := by
    apply sq_trans.dequeue
    · unfold SipT8
      apply st_trans.extC
      exact List.mem_cons.mpr (Or.inl rfl)
    · rfl
  have hmem : ("ClientA", (SipT8, [mProxyTrying, mProxyRinging, mProxyOK])) ∈ S80 := by simp [S80]
  exact net_trans.dequeue hSQ hmem
theorem tW81 : net_trans S81 (net_label.τ_dequeue "ClientA" "Proxy" "Ringing" "unit") S87 := by
  have hSQ : sq_trans (SipT6, [mProxyRinging]) (sq_action.dequeue "Proxy" "Ringing" "unit") (SipT3, []) := by
    apply sq_trans.dequeue
    · unfold SipT6
      apply st_trans.extC
      exact List.mem_cons.mpr (Or.inl rfl)
    · rfl
  have hmem : ("ClientA", (SipT6, [mProxyRinging])) ∈ S81 := by simp [S81]
  exact net_trans.dequeue hSQ hmem
theorem tW82 : net_trans S82 (net_label.τ_dequeue "ClientA" "Proxy" "Trying" "unit") S89 := by
  have hSQ : sq_trans (SipT8, [mProxyTrying, mProxyRinging, mProxyError]) (sq_action.dequeue "Proxy" "Trying" "unit") (SipT6, [mProxyRinging, mProxyError]) := by
    apply sq_trans.dequeue
    · unfold SipT8
      apply st_trans.extC
      exact List.mem_cons.mpr (Or.inl rfl)
    · rfl
  have hmem : ("ClientA", (SipT8, [mProxyTrying, mProxyRinging, mProxyError])) ∈ S82 := by simp [S82]
  exact net_trans.dequeue hSQ hmem
theorem tW83 : net_trans S83 (net_label.τ_dequeue "ClientA" "Proxy" "Ringing" "unit") S90 := by
  have hSQ : sq_trans (SipT6, [mProxyRinging]) (sq_action.dequeue "Proxy" "Ringing" "unit") (SipT3, []) := by
    apply sq_trans.dequeue
    · unfold SipT6
      apply st_trans.extC
      exact List.mem_cons.mpr (Or.inl rfl)
    · rfl
  have hmem : ("ClientA", (SipT6, [mProxyRinging])) ∈ S83 := by simp [S83]
  exact net_trans.dequeue hSQ hmem
theorem tW84 : net_trans S84 (net_label.τ_comm "Proxy" "ClientA" "OK" "unit") S92 := by
  have h_send : sq_trans (SipT1, []) (sq_action.send "ClientA" "OK" "unit") (SessionType.tEnd, []) := by
    apply sq_trans.send
    unfold SipT1
    apply st_trans.intC
    exact List.mem_cons.mpr (Or.inl rfl)
  have h_recv : sq_trans (SipT3, []) (sq_action.recv "Proxy" "OK" "unit") (SipT3, [] ++ [QueueMessage.msg "Proxy" "OK" "unit"]) :=
    sq_trans.recv
  have hmem_p : ("Proxy", (SipT1, [])) ∈ S84 := by simp [S84]
  have hmem_q : ("ClientA", (SipT3, [])) ∈ S84 := by simp [S84]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q
theorem tW85 : net_trans S85 (net_label.τ_comm "Proxy" "ClientA" "Error" "unit") S93 := by
  have h_send : sq_trans (SipT0, []) (sq_action.send "ClientA" "Error" "unit") (SessionType.tEnd, []) := by
    apply sq_trans.send
    unfold SipT0
    apply st_trans.intC
    exact List.mem_cons.mpr (Or.inl rfl)
  have h_recv : sq_trans (SipT3, []) (sq_action.recv "Proxy" "Error" "unit") (SipT3, [] ++ [QueueMessage.msg "Proxy" "Error" "unit"]) :=
    sq_trans.recv
  have hmem_p : ("Proxy", (SipT0, [])) ∈ S85 := by simp [S85]
  have hmem_q : ("ClientA", (SipT3, [])) ∈ S85 := by simp [S85]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q
theorem tW86 : net_trans S86 (net_label.τ_dequeue "ClientA" "Proxy" "Ringing" "unit") S92 := by
  have hSQ : sq_trans (SipT6, [mProxyRinging, mProxyOK]) (sq_action.dequeue "Proxy" "Ringing" "unit") (SipT3, [mProxyOK]) := by
    apply sq_trans.dequeue
    · unfold SipT6
      apply st_trans.extC
      exact List.mem_cons.mpr (Or.inl rfl)
    · rfl
  have hmem : ("ClientA", (SipT6, [mProxyRinging, mProxyOK])) ∈ S86 := by simp [S86]
  exact net_trans.dequeue hSQ hmem
theorem tW87 : net_trans S87 (net_label.τ_comm "Proxy" "ClientA" "OK" "unit") S92 := by
  have h_send : sq_trans (SipT1, []) (sq_action.send "ClientA" "OK" "unit") (SessionType.tEnd, []) := by
    apply sq_trans.send
    unfold SipT1
    apply st_trans.intC
    exact List.mem_cons.mpr (Or.inl rfl)
  have h_recv : sq_trans (SipT3, []) (sq_action.recv "Proxy" "OK" "unit") (SipT3, [] ++ [QueueMessage.msg "Proxy" "OK" "unit"]) :=
    sq_trans.recv
  have hmem_p : ("Proxy", (SipT1, [])) ∈ S87 := by simp [S87]
  have hmem_q : ("ClientA", (SipT3, [])) ∈ S87 := by simp [S87]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q
theorem tW88 : net_trans S88 (net_label.τ_comm "Proxy" "ClientA" "OK" "unit") S92 := by
  have h_send : sq_trans (SipT1, []) (sq_action.send "ClientA" "OK" "unit") (SessionType.tEnd, []) := by
    apply sq_trans.send
    unfold SipT1
    apply st_trans.intC
    exact List.mem_cons.mpr (Or.inl rfl)
  have h_recv : sq_trans (SipT3, []) (sq_action.recv "Proxy" "OK" "unit") (SipT3, [] ++ [QueueMessage.msg "Proxy" "OK" "unit"]) :=
    sq_trans.recv
  have hmem_p : ("Proxy", (SipT1, [])) ∈ S88 := by simp [S88]
  have hmem_q : ("ClientA", (SipT3, [])) ∈ S88 := by simp [S88]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q
theorem tW89 : net_trans S89 (net_label.τ_dequeue "ClientA" "Proxy" "Ringing" "unit") S93 := by
  have hSQ : sq_trans (SipT6, [mProxyRinging, mProxyError]) (sq_action.dequeue "Proxy" "Ringing" "unit") (SipT3, [mProxyError]) := by
    apply sq_trans.dequeue
    · unfold SipT6
      apply st_trans.extC
      exact List.mem_cons.mpr (Or.inl rfl)
    · rfl
  have hmem : ("ClientA", (SipT6, [mProxyRinging, mProxyError])) ∈ S89 := by simp [S89]
  exact net_trans.dequeue hSQ hmem
theorem tW90 : net_trans S90 (net_label.τ_comm "Proxy" "ClientA" "Error" "unit") S93 := by
  have h_send : sq_trans (SipT0, []) (sq_action.send "ClientA" "Error" "unit") (SessionType.tEnd, []) := by
    apply sq_trans.send
    unfold SipT0
    apply st_trans.intC
    exact List.mem_cons.mpr (Or.inl rfl)
  have h_recv : sq_trans (SipT3, []) (sq_action.recv "Proxy" "Error" "unit") (SipT3, [] ++ [QueueMessage.msg "Proxy" "Error" "unit"]) :=
    sq_trans.recv
  have hmem_p : ("Proxy", (SipT0, [])) ∈ S90 := by simp [S90]
  have hmem_q : ("ClientA", (SipT3, [])) ∈ S90 := by simp [S90]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q
theorem tW91 : net_trans S91 (net_label.τ_comm "Proxy" "ClientA" "Error" "unit") S93 := by
  have h_send : sq_trans (SipT0, []) (sq_action.send "ClientA" "Error" "unit") (SessionType.tEnd, []) := by
    apply sq_trans.send
    unfold SipT0
    apply st_trans.intC
    exact List.mem_cons.mpr (Or.inl rfl)
  have h_recv : sq_trans (SipT3, []) (sq_action.recv "Proxy" "Error" "unit") (SipT3, [] ++ [QueueMessage.msg "Proxy" "Error" "unit"]) :=
    sq_trans.recv
  have hmem_p : ("Proxy", (SipT0, [])) ∈ S91 := by simp [S91]
  have hmem_q : ("ClientA", (SipT3, [])) ∈ S91 := by simp [S91]
  exact net_trans.comm (by decide) h_send h_recv hmem_p hmem_q
theorem tW92 : net_trans S92 (net_label.τ_dequeue "ClientA" "Proxy" "OK" "unit") S71 := by
  have hSQ : sq_trans (SipT3, [mProxyOK]) (sq_action.dequeue "Proxy" "OK" "unit") (SessionType.tEnd, []) := by
    apply sq_trans.dequeue
    · unfold SipT3
      apply st_trans.extC
      exact List.mem_cons.mpr (Or.inl rfl)
    · rfl
  have hmem : ("ClientA", (SipT3, [mProxyOK])) ∈ S92 := by simp [S92]
  exact net_trans.dequeue hSQ hmem
theorem tW93 : net_trans S93 (net_label.τ_dequeue "ClientA" "Proxy" "Error" "unit") S71 := by
  have hSQ : sq_trans (SipT3, [mProxyError]) (sq_action.dequeue "Proxy" "Error" "unit") (SessionType.tEnd, []) := by
    apply sq_trans.dequeue
    · unfold SipT3
      apply st_trans.extC
      exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
    · rfl
  have hmem : ("ClientA", (SipT3, [mProxyError])) ∈ S93 := by simp [S93]
  exact net_trans.dequeue hSQ hmem

-- Reachability (generated).
theorem sipReach_aux : ∀ (N1 N2 : Network), net_trans_star N1 N2 →
    (N1 = S0 ∨ N1 = S1 ∨ N1 = S2 ∨ N1 = S3 ∨ N1 = S4 ∨ N1 = S5 ∨ N1 = S6 ∨ N1 = S7 ∨ N1 = S8 ∨ N1 = S9 ∨ N1 = S10 ∨ N1 = S11 ∨ N1 = S12 ∨ N1 = S13 ∨ N1 = S14 ∨ N1 = S15 ∨ N1 = S16 ∨ N1 = S17 ∨ N1 = S18 ∨ N1 = S19 ∨ N1 = S20 ∨ N1 = S21 ∨ N1 = S22 ∨ N1 = S23 ∨ N1 = S24 ∨ N1 = S25 ∨ N1 = S26 ∨ N1 = S27 ∨ N1 = S28 ∨ N1 = S29 ∨ N1 = S30 ∨ N1 = S31 ∨ N1 = S32 ∨ N1 = S33 ∨ N1 = S34 ∨ N1 = S35 ∨ N1 = S36 ∨ N1 = S37 ∨ N1 = S38 ∨ N1 = S39 ∨ N1 = S40 ∨ N1 = S41 ∨ N1 = S42 ∨ N1 = S43 ∨ N1 = S44 ∨ N1 = S45 ∨ N1 = S46 ∨ N1 = S47 ∨ N1 = S48 ∨ N1 = S49 ∨ N1 = S50 ∨ N1 = S51 ∨ N1 = S52 ∨ N1 = S53 ∨ N1 = S54 ∨ N1 = S55 ∨ N1 = S56 ∨ N1 = S57 ∨ N1 = S58 ∨ N1 = S59 ∨ N1 = S60 ∨ N1 = S61 ∨ N1 = S62 ∨ N1 = S63 ∨ N1 = S64 ∨ N1 = S65 ∨ N1 = S66 ∨ N1 = S67 ∨ N1 = S68 ∨ N1 = S69 ∨ N1 = S70 ∨ N1 = S71 ∨ N1 = S72 ∨ N1 = S73 ∨ N1 = S74 ∨ N1 = S75 ∨ N1 = S76 ∨ N1 = S77 ∨ N1 = S78 ∨ N1 = S79 ∨ N1 = S80 ∨ N1 = S81 ∨ N1 = S82 ∨ N1 = S83 ∨ N1 = S84 ∨ N1 = S85 ∨ N1 = S86 ∨ N1 = S87 ∨ N1 = S88 ∨ N1 = S89 ∨ N1 = S90 ∨ N1 = S91 ∨ N1 = S92 ∨ N1 = S93) →
    (N2 = S0 ∨ N2 = S1 ∨ N2 = S2 ∨ N2 = S3 ∨ N2 = S4 ∨ N2 = S5 ∨ N2 = S6 ∨ N2 = S7 ∨ N2 = S8 ∨ N2 = S9 ∨ N2 = S10 ∨ N2 = S11 ∨ N2 = S12 ∨ N2 = S13 ∨ N2 = S14 ∨ N2 = S15 ∨ N2 = S16 ∨ N2 = S17 ∨ N2 = S18 ∨ N2 = S19 ∨ N2 = S20 ∨ N2 = S21 ∨ N2 = S22 ∨ N2 = S23 ∨ N2 = S24 ∨ N2 = S25 ∨ N2 = S26 ∨ N2 = S27 ∨ N2 = S28 ∨ N2 = S29 ∨ N2 = S30 ∨ N2 = S31 ∨ N2 = S32 ∨ N2 = S33 ∨ N2 = S34 ∨ N2 = S35 ∨ N2 = S36 ∨ N2 = S37 ∨ N2 = S38 ∨ N2 = S39 ∨ N2 = S40 ∨ N2 = S41 ∨ N2 = S42 ∨ N2 = S43 ∨ N2 = S44 ∨ N2 = S45 ∨ N2 = S46 ∨ N2 = S47 ∨ N2 = S48 ∨ N2 = S49 ∨ N2 = S50 ∨ N2 = S51 ∨ N2 = S52 ∨ N2 = S53 ∨ N2 = S54 ∨ N2 = S55 ∨ N2 = S56 ∨ N2 = S57 ∨ N2 = S58 ∨ N2 = S59 ∨ N2 = S60 ∨ N2 = S61 ∨ N2 = S62 ∨ N2 = S63 ∨ N2 = S64 ∨ N2 = S65 ∨ N2 = S66 ∨ N2 = S67 ∨ N2 = S68 ∨ N2 = S69 ∨ N2 = S70 ∨ N2 = S71 ∨ N2 = S72 ∨ N2 = S73 ∨ N2 = S74 ∨ N2 = S75 ∨ N2 = S76 ∨ N2 = S77 ∨ N2 = S78 ∨ N2 = S79 ∨ N2 = S80 ∨ N2 = S81 ∨ N2 = S82 ∨ N2 = S83 ∨ N2 = S84 ∨ N2 = S85 ∨ N2 = S86 ∨ N2 = S87 ∨ N2 = S88 ∨ N2 = S89 ∨ N2 = S90 ∨ N2 = S91 ∨ N2 = S92 ∨ N2 = S93) := by
  intro N1 N2 hStar
  induction hStar with
  | refl => intro h; exact h
  | step hInt hTr _ ih =>
    intro hN1
    rcases hN1 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h := S0_step _ _ hTr hInt
      subst h
      exact ih (Or.inr (Or.inl rfl))
    · have h := S1_step _ _ hTr hInt
      subst h
      exact ih (Or.inr (Or.inr (Or.inl rfl)))
    · have h := S2_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    · have h := S3_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
    · have h := S4_step _ _ hTr hInt
      subst h
      exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
    · have h := S5_step _ _ hTr hInt
      rcases h with rfl | rfl | rfl
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))
    · have h := S6_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))
    · exact absurd (S7_no_step _ _ hTr hInt) id
    · have h := S8_step _ _ hTr hInt
      rcases h with rfl | rfl | rfl
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))
    · have h := S9_step _ _ hTr hInt
      subst h
      exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))
    · have h := S10_step _ _ hTr hInt
      rcases h with rfl | rfl | rfl
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))))
    · have h := S11_step _ _ hTr hInt
      subst h
      exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))))
    · have h := S12_step _ _ hTr hInt
      rcases h with rfl | rfl | rfl
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))))
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))))))
    · have h := S13_step _ _ hTr hInt
      rcases h with rfl | rfl | rfl | rfl
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))))))
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))))))))
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))))))))
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))))))))))
    · have h := S14_step _ _ hTr hInt
      subst h
      exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))))))))))
    · have h := S15_step _ _ hTr hInt
      subst h
      exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))))))))))))
    · have h := S16_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))))))))))))
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))))))))))))))
    · have h := S17_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))))))))))))))
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))))))))))))))))
    · have h := S18_step _ _ hTr hInt
      rcases h with rfl | rfl | rfl | rfl
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))))))))))))))))
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))))))))
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))))))))))
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))))))
    · have h := S19_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))))))))))))))))))
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))))))))))))
    · have h := S20_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))))))))))))))
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))))))))))))))))
    · have h := S21_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))))))))))))))
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))))))))))))))))
    · have h := S22_step _ _ hTr hInt
      rcases h with rfl | rfl | rfl
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))))))))))))))))))
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))))))))))))))))))))
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))))))))))))))))))))
    · have h := S23_step _ _ hTr hInt
      rcases h with rfl | rfl | rfl | rfl
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))))))))))))))))))))))
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))
    · have h := S24_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))
    · have h := S25_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))
    · have h := S26_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))
    · have h := S27_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))
    · have h := S28_step _ _ hTr hInt
      subst h
      exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))
    · have h := S29_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))
    · have h := S30_step _ _ hTr hInt
      rcases h with rfl | rfl | rfl
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))))
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))))))))))))))))))))
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))))))))))))))))))))
    · have h := S31_step _ _ hTr hInt
      subst h
      exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))
    · have h := S32_step _ _ hTr hInt
      rcases h with rfl | rfl | rfl | rfl
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))))))))))))))))))))))
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))
    · have h := S33_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))
    · have h := S34_step _ _ hTr hInt
      rcases h with rfl | rfl | rfl
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))))))
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))))))))
    · have h := S35_step _ _ hTr hInt
      subst h
      exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))
    · have h := S36_step _ _ hTr hInt
      subst h
      exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))))))))
    · have h := S37_step _ _ hTr hInt
      rcases h with rfl | rfl | rfl
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))))))
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · have h := S38_step _ _ hTr hInt
      rcases h with rfl | rfl | rfl
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))))))
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))))))))
    · have h := S39_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · have h := S40_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · have h := S41_step _ _ hTr hInt
      subst h
      exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · have h := S42_step _ _ hTr hInt
      subst h
      exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · have h := S43_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · have h := S44_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · have h := S45_step _ _ hTr hInt
      subst h
      exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · have h := S46_step _ _ hTr hInt
      subst h
      exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · have h := S47_step _ _ hTr hInt
      subst h
      exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · have h := S48_step _ _ hTr hInt
      rcases h with rfl | rfl | rfl
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))))))
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))))))))
    · have h := S49_step _ _ hTr hInt
      subst h
      exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · have h := S50_step _ _ hTr hInt
      rcases h with rfl | rfl | rfl
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · have h := S51_step _ _ hTr hInt
      subst h
      exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · have h := S52_step _ _ hTr hInt
      subst h
      exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · have h := S53_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · have h := S54_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · have h := S55_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · have h := S56_step _ _ hTr hInt
      subst h
      exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · have h := S57_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · have h := S58_step _ _ hTr hInt
      subst h
      exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · have h := S59_step _ _ hTr hInt
      subst h
      exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · have h := S60_step _ _ hTr hInt
      subst h
      exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · have h := S61_step _ _ hTr hInt
      subst h
      exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · have h := S62_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · have h := S63_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · have h := S64_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · have h := S65_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · have h := S66_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · have h := S67_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · have h := S68_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · have h := S69_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · have h := S70_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · exact absurd (S71_no_step _ _ hTr hInt) id
    · have h := S72_step _ _ hTr hInt
      subst h
      exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · have h := S73_step _ _ hTr hInt
      subst h
      exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · have h := S74_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · have h := S75_step _ _ hTr hInt
      subst h
      exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · have h := S76_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · have h := S77_step _ _ hTr hInt
      subst h
      exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · have h := S78_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · have h := S79_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · have h := S80_step _ _ hTr hInt
      subst h
      exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · have h := S81_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · have h := S82_step _ _ hTr hInt
      subst h
      exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · have h := S83_step _ _ hTr hInt
      rcases h with rfl | rfl
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      · exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · have h := S84_step _ _ hTr hInt
      subst h
      exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · have h := S85_step _ _ hTr hInt
      subst h
      exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · have h := S86_step _ _ hTr hInt
      subst h
      exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · have h := S87_step _ _ hTr hInt
      subst h
      exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · have h := S88_step _ _ hTr hInt
      subst h
      exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · have h := S89_step _ _ hTr hInt
      subst h
      exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · have h := S90_step _ _ hTr hInt
      subst h
      exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · have h := S91_step _ _ hTr hInt
      subst h
      exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · have h := S92_step _ _ hTr hInt
      subst h
      exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · have h := S93_step _ _ hTr hInt
      subst h
      exact ih (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem sipReach : ∀ (N' : Network), net_trans_star Net N' →
    (N' = S0 ∨ N' = S1 ∨ N' = S2 ∨ N' = S3 ∨ N' = S4 ∨ N' = S5 ∨ N' = S6 ∨ N' = S7 ∨ N' = S8 ∨ N' = S9 ∨ N' = S10 ∨ N' = S11 ∨ N' = S12 ∨ N' = S13 ∨ N' = S14 ∨ N' = S15 ∨ N' = S16 ∨ N' = S17 ∨ N' = S18 ∨ N' = S19 ∨ N' = S20 ∨ N' = S21 ∨ N' = S22 ∨ N' = S23 ∨ N' = S24 ∨ N' = S25 ∨ N' = S26 ∨ N' = S27 ∨ N' = S28 ∨ N' = S29 ∨ N' = S30 ∨ N' = S31 ∨ N' = S32 ∨ N' = S33 ∨ N' = S34 ∨ N' = S35 ∨ N' = S36 ∨ N' = S37 ∨ N' = S38 ∨ N' = S39 ∨ N' = S40 ∨ N' = S41 ∨ N' = S42 ∨ N' = S43 ∨ N' = S44 ∨ N' = S45 ∨ N' = S46 ∨ N' = S47 ∨ N' = S48 ∨ N' = S49 ∨ N' = S50 ∨ N' = S51 ∨ N' = S52 ∨ N' = S53 ∨ N' = S54 ∨ N' = S55 ∨ N' = S56 ∨ N' = S57 ∨ N' = S58 ∨ N' = S59 ∨ N' = S60 ∨ N' = S61 ∨ N' = S62 ∨ N' = S63 ∨ N' = S64 ∨ N' = S65 ∨ N' = S66 ∨ N' = S67 ∨ N' = S68 ∨ N' = S69 ∨ N' = S70 ∨ N' = S71 ∨ N' = S72 ∨ N' = S73 ∨ N' = S74 ∨ N' = S75 ∨ N' = S76 ∨ N' = S77 ∨ N' = S78 ∨ N' = S79 ∨ N' = S80 ∨ N' = S81 ∨ N' = S82 ∨ N' = S83 ∨ N' = S84 ∨ N' = S85 ∨ N' = S86 ∨ N' = S87 ∨ N' = S88 ∨ N' = S89 ∨ N' = S90 ∨ N' = S91 ∨ N' = S92 ∨ N' = S93) :=
  fun N' hStar => sipReach_aux Net N' hStar (Or.inl rfl)

-- Half-duplex (generated).
theorem Net_halfDuplex : IsHalfDuplex Net := by
  intro N' hStar p q Qp Qq hP hQ hCp hCq
  have hR := sipReach N' hStar
  rcases hR with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- S0
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S0, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S1
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S1, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S2
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S2, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S3
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S3, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S4
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S4, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S5
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S5, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S6
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S6, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
  · -- S7
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S7, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S8
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S8, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S9
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S9, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S10
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S10, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S11
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S11, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
  · -- S12
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S12, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S13
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S13, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S14
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S14, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S15
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S15, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S16
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S16, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S17
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S17, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S18
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S18, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
  · -- S19
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S19, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
  · -- S20
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S20, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S21
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S21, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S22
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S22, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S23
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S23, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S24
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S24, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
  · -- S25
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S25, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
  · -- S26
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S26, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S27
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S27, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S28
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S28, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S29
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S29, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S30
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S30, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S31
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S31, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S32
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S32, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
  · -- S33
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S33, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
  · -- S34
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S34, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S35
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S35, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S36
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S36, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S37
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S37, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S38
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S38, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S39
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S39, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
  · -- S40
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S40, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
  · -- S41
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S41, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S42
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S42, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S43
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S43, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S44
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S44, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S45
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S45, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S46
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S46, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S47
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S47, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S48
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S48, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S49
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S49, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S50
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S50, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S51
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S51, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S52
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S52, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S53
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S53, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
  · -- S54
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S54, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
  · -- S55
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S55, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S56
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S56, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S57
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S57, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S58
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S58, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S59
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S59, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S60
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S60, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S61
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S61, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S62
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S62, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S63
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S63, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
  · -- S64
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S64, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
  · -- S65
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S65, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S66
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S66, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S67
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S67, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
  · -- S68
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S68, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
  · -- S69
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S69, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S70
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S70, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S71
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S71, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S72
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S72, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S73
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S73, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S74
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S74, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
  · -- S75
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S75, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S76
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S76, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
  · -- S77
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S77, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S78
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S78, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S79
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S79, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S80
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S80, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S81
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S81, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S82
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S82, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S83
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S83, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S84
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S84, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S85
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S85, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S86
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S86, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S87
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S87, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S88
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S88, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S89
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S89, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S90
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S90, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S91
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S91, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S92
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S92, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
  · -- S93
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [S93, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact noContainsNil hCq
    · obtain ⟨lab, S, hmem⟩ := hCp
      have hmem' := hmem.to_mem
      simp at hmem'
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil
    · exact absurd hCp noContainsNil

-- Output-liveness, finite part (generated).
theorem sipOL_stuck : ∀ (N' : Network), net_trans_star Net N' →
    IsStuckNetwork N' → NoOrphanMessages N' := by
  intro N' hStar hStuck
  have hR := sipReach N' hStar
  rcases hR with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW0⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW1⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW2⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW3⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW4⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW5⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW6⟩
  · intro r T Q p lab S Q' hmem hQ
    simp only [S7, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW8⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW9⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW10⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW11⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW12⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW13⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW14⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW15⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW16⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW17⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW18⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW19⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW20⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW21⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW22⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW23⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW24⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW25⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW26⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW27⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW28⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW29⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW30⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW31⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW32⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW33⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW34⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW35⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW36⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW37⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW38⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW39⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW40⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW41⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW42⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW43⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW44⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW45⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW46⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW47⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW48⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW49⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW50⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW51⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW52⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW53⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW54⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW55⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW56⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW57⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW58⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW59⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW60⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW61⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW62⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW63⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW64⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW65⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW66⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW67⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW68⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW69⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW70⟩
  · intro r T Q p lab S Q' hmem hQ
    simp only [S71, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW72⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW73⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW74⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW75⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW76⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW77⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW78⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW79⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW80⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW81⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW82⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW83⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW84⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW85⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW86⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW87⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW88⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW89⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW90⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW91⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW92⟩
  · exfalso
    exact hStuck ⟨_, _, by trivial, tW93⟩

/-- `Net` is output-live: fair paths drain queues, stuck states are clean. -/
theorem Net_outputLive : IsOutputLiveNetwork Net :=
  ⟨Net_outputLiveInfinite, sipOL_stuck⟩


end Sip

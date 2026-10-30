import Nest.Examples.StoreHD

namespace Store


theorem storeOL_inf : IsOutputLiveInfinitePathNetwork Net := by
  intro path h0 hfair i p Qp hmemP q lab S hdeq
  have hStar : net_trans_star Net (path.seq i) := path_star_reachable h0 i
  have hR := storeCover _ hStar
  rcases hR with ⟨C, hCmem, hperm⟩
  simp only [Cs, List.mem_cons, List.mem_nil_iff, or_false] at hCmem
  rcases hCmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- CS_0
    have hP_C : NetworkHasQueue CS_0 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_0, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_1
    have hP_C : NetworkHasQueue CS_1 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_1, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mECPlaceOrder] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans HTTP (st_label.inp "ExternalClient" "PlaceOrder" "unit") H1 :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mECPlaceOrder] (QueueMessage.msg "ExternalClient" "PlaceOrder" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("HTTP_Gateway", (HTTP, [mECPlaceOrder])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_1])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "HTTP_Gateway" "ExternalClient" "PlaceOrder" "unit") ((path.seq i).replace "HTTP_Gateway" (H1, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "HTTP_Gateway" "ExternalClient" "PlaceOrder" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_2
    have hP_C : NetworkHasQueue CS_2 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_2, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_3
    have hP_C : NetworkHasQueue CS_3 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_3, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGGetSKUDetails] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans Inventory (st_label.inp "HTTP_Gateway" "GetSKUDetails" "unit") InvA :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mHGGetSKUDetails] (QueueMessage.msg "HTTP_Gateway" "GetSKUDetails" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("Inventory", (Inventory, [mHGGetSKUDetails])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_3])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "Inventory" "HTTP_Gateway" "GetSKUDetails" "unit") ((path.seq i).replace "Inventory" (InvA, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "Inventory" "HTTP_Gateway" "GetSKUDetails" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_4
    have hP_C : NetworkHasQueue CS_4 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_4, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_5
    have hP_C : NetworkHasQueue CS_5 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_5, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mInvSKUDetails] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans H2 (st_label.inp "Inventory" "SKUDetails" "unit") H3 :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mInvSKUDetails] (QueueMessage.msg "Inventory" "SKUDetails" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("HTTP_Gateway", (H2, [mInvSKUDetails])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_5])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "HTTP_Gateway" "Inventory" "SKUDetails" "unit") ((path.seq i).replace "HTTP_Gateway" (H3, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "HTTP_Gateway" "Inventory" "SKUDetails" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_6
    have hP_C : NetworkHasQueue CS_6 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_6, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_7
    have hP_C : NetworkHasQueue CS_7 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_7, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGSKUDetails] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans StCB0 (st_label.inp "HTTP_Gateway" "SKUDetails" "unit") StRec :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mHGSKUDetails] (QueueMessage.msg "HTTP_Gateway" "SKUDetails" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("ExternalClient", (StCB0, [mHGSKUDetails])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_7])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "SKUDetails" "unit") ((path.seq i).replace "ExternalClient" (StRec, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "ExternalClient" "HTTP_Gateway" "SKUDetails" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_8
    have hP_C : NetworkHasQueue CS_8 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_8, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_9
    have hP_C : NetworkHasQueue CS_9 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_9, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mECConfirmOrder] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans HRec (st_label.inp "ExternalClient" "ConfirmOrder" "unit") H4p :=
        st_transb_sound (n := 2) (by decide)
      have hQdeq : Queue.dequeue [mECConfirmOrder] (QueueMessage.msg "ExternalClient" "ConfirmOrder" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("HTTP_Gateway", (HRec, [mECConfirmOrder])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_9])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "HTTP_Gateway" "ExternalClient" "ConfirmOrder" "unit") ((path.seq i).replace "HTTP_Gateway" (H4p, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "HTTP_Gateway" "ExternalClient" "ConfirmOrder" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_10
    have hP_C : NetworkHasQueue CS_10 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_10, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mECCancelOrder] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans HRec (st_label.inp "ExternalClient" "CancelOrder" "unit") H5 :=
        st_transb_sound (n := 2) (by decide)
      have hQdeq : Queue.dequeue [mECCancelOrder] (QueueMessage.msg "ExternalClient" "CancelOrder" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("HTTP_Gateway", (HRec, [mECCancelOrder])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_10])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "HTTP_Gateway" "ExternalClient" "CancelOrder" "unit") ((path.seq i).replace "HTTP_Gateway" (H5, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "HTTP_Gateway" "ExternalClient" "CancelOrder" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_11
    have hP_C : NetworkHasQueue CS_11 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_11, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_12
    have hP_C : NetworkHasQueue CS_12 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_12, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_13
    have hP_C : NetworkHasQueue CS_13 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_13, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGVerifyCC] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans Payment (st_label.inp "HTTP_Gateway" "VerifyCC" "unit") PayISub :=
        st_transb_sound (n := 2) (by decide)
      have hQdeq : Queue.dequeue [mHGVerifyCC] (QueueMessage.msg "HTTP_Gateway" "VerifyCC" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("Payment", (Payment, [mHGVerifyCC])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_13])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "Payment" "HTTP_Gateway" "VerifyCC" "unit") ((path.seq i).replace "Payment" (PayISub, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "Payment" "HTTP_Gateway" "VerifyCC" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_14
    have hP_C : NetworkHasQueue CS_14 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_14, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGCancel] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans StCancTp (st_label.inp "HTTP_Gateway" "Cancel" "unit") SessionType.tEnd :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mHGCancel] (QueueMessage.msg "HTTP_Gateway" "Cancel" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("ExternalClient", (StCancTp, [mHGCancel])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_14])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "Cancel" "unit") ((path.seq i).replace "ExternalClient" (SessionType.tEnd, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "ExternalClient" "HTTP_Gateway" "Cancel" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_15
    have hP_C : NetworkHasQueue CS_15 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_15, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_16
    have hP_C : NetworkHasQueue CS_16 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_16, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_17
    have hP_C : NetworkHasQueue CS_17 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_17, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mPayValidCC] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans H6p (st_label.inp "Payment" "ValidCC" "unit") H7 :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mPayValidCC] (QueueMessage.msg "Payment" "ValidCC" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("HTTP_Gateway", (H6p, [mPayValidCC])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_17])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "HTTP_Gateway" "Payment" "ValidCC" "unit") ((path.seq i).replace "HTTP_Gateway" (H7, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "HTTP_Gateway" "Payment" "ValidCC" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_18
    have hP_C : NetworkHasQueue CS_18 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_18, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mPayInvalidCC] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans H6p (st_label.inp "Payment" "InvalidCC" "unit") H8p :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mPayInvalidCC] (QueueMessage.msg "Payment" "InvalidCC" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("HTTP_Gateway", (H6p, [mPayInvalidCC])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_18])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "HTTP_Gateway" "Payment" "InvalidCC" "unit") ((path.seq i).replace "HTTP_Gateway" (H8p, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "HTTP_Gateway" "Payment" "InvalidCC" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_19
    have hP_C : NetworkHasQueue CS_19 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_19, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_20
    have hP_C : NetworkHasQueue CS_20 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_20, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_21
    have hP_C : NetworkHasQueue CS_21 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_21, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGMakeCharge] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans PayTa (st_label.inp "HTTP_Gateway" "MakeCharge" "unit") PayIBank :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mHGMakeCharge] (QueueMessage.msg "HTTP_Gateway" "MakeCharge" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("Payment", (PayTa, [mHGMakeCharge])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_21])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "Payment" "HTTP_Gateway" "MakeCharge" "unit") ((path.seq i).replace "Payment" (PayIBank, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "Payment" "HTTP_Gateway" "MakeCharge" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_22
    have hP_C : NetworkHasQueue CS_22 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_22, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGInvalidCC] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans StConfTp (st_label.inp "HTTP_Gateway" "InvalidCC" "unit") StRec :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mHGInvalidCC] (QueueMessage.msg "HTTP_Gateway" "InvalidCC" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("ExternalClient", (StConfTp, [mHGInvalidCC])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_22])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "InvalidCC" "unit") ((path.seq i).replace "ExternalClient" (StRec, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "ExternalClient" "HTTP_Gateway" "InvalidCC" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_23
    have hP_C : NetworkHasQueue CS_23 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_23, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_24
    have hP_C : NetworkHasQueue CS_24 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_24, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGMakeOrder] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans InvB (st_label.inp "HTTP_Gateway" "MakeOrder" "unit") InvC :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mHGMakeOrder] (QueueMessage.msg "HTTP_Gateway" "MakeOrder" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("Inventory", (InvB, [mHGMakeOrder])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_24])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "Inventory" "HTTP_Gateway" "MakeOrder" "unit") ((path.seq i).replace "Inventory" (InvC, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "Inventory" "HTTP_Gateway" "MakeOrder" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGMakeCharge] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans PayTa (st_label.inp "HTTP_Gateway" "MakeCharge" "unit") PayIBank :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mHGMakeCharge] (QueueMessage.msg "HTTP_Gateway" "MakeCharge" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("Payment", (PayTa, [mHGMakeCharge])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_24])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "Payment" "HTTP_Gateway" "MakeCharge" "unit") ((path.seq i).replace "Payment" (PayIBank, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "Payment" "HTTP_Gateway" "MakeCharge" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_25
    have hP_C : NetworkHasQueue CS_25 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_25, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mPayMakeCharge] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans Bank (st_label.inp "Payment" "MakeCharge" "unit") SessionType.tEnd :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mPayMakeCharge] (QueueMessage.msg "Payment" "MakeCharge" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("ExternalBank", (Bank, [mPayMakeCharge])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_25])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit") ((path.seq i).replace "ExternalBank" (SessionType.tEnd, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "ExternalBank" "Payment" "MakeCharge" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_26
    have hP_C : NetworkHasQueue CS_26 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_26, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGMakeOrder] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans InvB (st_label.inp "HTTP_Gateway" "MakeOrder" "unit") InvC :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mHGMakeOrder] (QueueMessage.msg "HTTP_Gateway" "MakeOrder" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("Inventory", (InvB, [mHGMakeOrder])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_26])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "Inventory" "HTTP_Gateway" "MakeOrder" "unit") ((path.seq i).replace "Inventory" (InvC, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "Inventory" "HTTP_Gateway" "MakeOrder" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_27
    have hP_C : NetworkHasQueue CS_27 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_27, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGMakeCharge] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans PayTa (st_label.inp "HTTP_Gateway" "MakeCharge" "unit") PayIBank :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mHGMakeCharge] (QueueMessage.msg "HTTP_Gateway" "MakeCharge" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("Payment", (PayTa, [mHGMakeCharge])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_27])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "Payment" "HTTP_Gateway" "MakeCharge" "unit") ((path.seq i).replace "Payment" (PayIBank, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "Payment" "HTTP_Gateway" "MakeCharge" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_28
    have hP_C : NetworkHasQueue CS_28 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_28, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGValidCC] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans StConfTp (st_label.inp "HTTP_Gateway" "ValidCC" "unit") SessionType.tEnd :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mHGValidCC] (QueueMessage.msg "HTTP_Gateway" "ValidCC" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("ExternalClient", (StConfTp, [mHGValidCC])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_28])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit") ((path.seq i).replace "ExternalClient" (SessionType.tEnd, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "ExternalClient" "HTTP_Gateway" "ValidCC" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGMakeOrder] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans InvB (st_label.inp "HTTP_Gateway" "MakeOrder" "unit") InvC :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mHGMakeOrder] (QueueMessage.msg "HTTP_Gateway" "MakeOrder" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("Inventory", (InvB, [mHGMakeOrder])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_28])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "Inventory" "HTTP_Gateway" "MakeOrder" "unit") ((path.seq i).replace "Inventory" (InvC, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "Inventory" "HTTP_Gateway" "MakeOrder" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGMakeCharge] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans PayTa (st_label.inp "HTTP_Gateway" "MakeCharge" "unit") PayIBank :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mHGMakeCharge] (QueueMessage.msg "HTTP_Gateway" "MakeCharge" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("Payment", (PayTa, [mHGMakeCharge])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_28])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "Payment" "HTTP_Gateway" "MakeCharge" "unit") ((path.seq i).replace "Payment" (PayIBank, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "Payment" "HTTP_Gateway" "MakeCharge" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_29
    have hP_C : NetworkHasQueue CS_29 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_29, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_30
    have hP_C : NetworkHasQueue CS_30 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_30, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mPayMakeCharge] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans Bank (st_label.inp "Payment" "MakeCharge" "unit") SessionType.tEnd :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mPayMakeCharge] (QueueMessage.msg "Payment" "MakeCharge" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("ExternalBank", (Bank, [mPayMakeCharge])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_30])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit") ((path.seq i).replace "ExternalBank" (SessionType.tEnd, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "ExternalBank" "Payment" "MakeCharge" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGMakeOrder] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans InvB (st_label.inp "HTTP_Gateway" "MakeOrder" "unit") InvC :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mHGMakeOrder] (QueueMessage.msg "HTTP_Gateway" "MakeOrder" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("Inventory", (InvB, [mHGMakeOrder])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_30])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "Inventory" "HTTP_Gateway" "MakeOrder" "unit") ((path.seq i).replace "Inventory" (InvC, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "Inventory" "HTTP_Gateway" "MakeOrder" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_31
    have hP_C : NetworkHasQueue CS_31 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_31, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_32
    have hP_C : NetworkHasQueue CS_32 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_32, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGValidCC] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans StConfTp (st_label.inp "HTTP_Gateway" "ValidCC" "unit") SessionType.tEnd :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mHGValidCC] (QueueMessage.msg "HTTP_Gateway" "ValidCC" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("ExternalClient", (StConfTp, [mHGValidCC])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_32])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit") ((path.seq i).replace "ExternalClient" (SessionType.tEnd, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "ExternalClient" "HTTP_Gateway" "ValidCC" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGMakeOrder] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans InvB (st_label.inp "HTTP_Gateway" "MakeOrder" "unit") InvC :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mHGMakeOrder] (QueueMessage.msg "HTTP_Gateway" "MakeOrder" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("Inventory", (InvB, [mHGMakeOrder])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_32])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "Inventory" "HTTP_Gateway" "MakeOrder" "unit") ((path.seq i).replace "Inventory" (InvC, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "Inventory" "HTTP_Gateway" "MakeOrder" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_33
    have hP_C : NetworkHasQueue CS_33 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_33, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGMakeCharge] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans PayTa (st_label.inp "HTTP_Gateway" "MakeCharge" "unit") PayIBank :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mHGMakeCharge] (QueueMessage.msg "HTTP_Gateway" "MakeCharge" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("Payment", (PayTa, [mHGMakeCharge])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_33])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "Payment" "HTTP_Gateway" "MakeCharge" "unit") ((path.seq i).replace "Payment" (PayIBank, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "Payment" "HTTP_Gateway" "MakeCharge" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mInvShipOrder] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans Shipping (st_label.inp "Inventory" "ShipOrder" "unit") ShipA :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mInvShipOrder] (QueueMessage.msg "Inventory" "ShipOrder" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("Shipping", (Shipping, [mInvShipOrder])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_33])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "Shipping" "Inventory" "ShipOrder" "unit") ((path.seq i).replace "Shipping" (ShipA, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "Shipping" "Inventory" "ShipOrder" "unit" ⟨_, hTr⟩
  · -- CS_34
    have hP_C : NetworkHasQueue CS_34 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_34, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGValidCC] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans StConfTp (st_label.inp "HTTP_Gateway" "ValidCC" "unit") SessionType.tEnd :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mHGValidCC] (QueueMessage.msg "HTTP_Gateway" "ValidCC" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("ExternalClient", (StConfTp, [mHGValidCC])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_34])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit") ((path.seq i).replace "ExternalClient" (SessionType.tEnd, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "ExternalClient" "HTTP_Gateway" "ValidCC" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGMakeCharge] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans PayTa (st_label.inp "HTTP_Gateway" "MakeCharge" "unit") PayIBank :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mHGMakeCharge] (QueueMessage.msg "HTTP_Gateway" "MakeCharge" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("Payment", (PayTa, [mHGMakeCharge])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_34])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "Payment" "HTTP_Gateway" "MakeCharge" "unit") ((path.seq i).replace "Payment" (PayIBank, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "Payment" "HTTP_Gateway" "MakeCharge" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_35
    have hP_C : NetworkHasQueue CS_35 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_35, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGMakeOrder] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans InvB (st_label.inp "HTTP_Gateway" "MakeOrder" "unit") InvC :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mHGMakeOrder] (QueueMessage.msg "HTTP_Gateway" "MakeOrder" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("Inventory", (InvB, [mHGMakeOrder])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_35])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "Inventory" "HTTP_Gateway" "MakeOrder" "unit") ((path.seq i).replace "Inventory" (InvC, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "Inventory" "HTTP_Gateway" "MakeOrder" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGMakeCharge] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans PayTa (st_label.inp "HTTP_Gateway" "MakeCharge" "unit") PayIBank :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mHGMakeCharge] (QueueMessage.msg "HTTP_Gateway" "MakeCharge" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("Payment", (PayTa, [mHGMakeCharge])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_35])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "Payment" "HTTP_Gateway" "MakeCharge" "unit") ((path.seq i).replace "Payment" (PayIBank, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "Payment" "HTTP_Gateway" "MakeCharge" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_36
    have hP_C : NetworkHasQueue CS_36 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_36, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGMakeOrder] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans InvB (st_label.inp "HTTP_Gateway" "MakeOrder" "unit") InvC :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mHGMakeOrder] (QueueMessage.msg "HTTP_Gateway" "MakeOrder" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("Inventory", (InvB, [mHGMakeOrder])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_36])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "Inventory" "HTTP_Gateway" "MakeOrder" "unit") ((path.seq i).replace "Inventory" (InvC, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "Inventory" "HTTP_Gateway" "MakeOrder" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_37
    have hP_C : NetworkHasQueue CS_37 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_37, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mPayMakeCharge] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans Bank (st_label.inp "Payment" "MakeCharge" "unit") SessionType.tEnd :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mPayMakeCharge] (QueueMessage.msg "Payment" "MakeCharge" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("ExternalBank", (Bank, [mPayMakeCharge])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_37])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit") ((path.seq i).replace "ExternalBank" (SessionType.tEnd, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "ExternalBank" "Payment" "MakeCharge" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_38
    have hP_C : NetworkHasQueue CS_38 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_38, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mPayMakeCharge] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans Bank (st_label.inp "Payment" "MakeCharge" "unit") SessionType.tEnd :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mPayMakeCharge] (QueueMessage.msg "Payment" "MakeCharge" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("ExternalBank", (Bank, [mPayMakeCharge])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_38])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit") ((path.seq i).replace "ExternalBank" (SessionType.tEnd, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "ExternalBank" "Payment" "MakeCharge" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGValidCC] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans StConfTp (st_label.inp "HTTP_Gateway" "ValidCC" "unit") SessionType.tEnd :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mHGValidCC] (QueueMessage.msg "HTTP_Gateway" "ValidCC" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("ExternalClient", (StConfTp, [mHGValidCC])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_38])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit") ((path.seq i).replace "ExternalClient" (SessionType.tEnd, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "ExternalClient" "HTTP_Gateway" "ValidCC" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGMakeOrder] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans InvB (st_label.inp "HTTP_Gateway" "MakeOrder" "unit") InvC :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mHGMakeOrder] (QueueMessage.msg "HTTP_Gateway" "MakeOrder" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("Inventory", (InvB, [mHGMakeOrder])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_38])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "Inventory" "HTTP_Gateway" "MakeOrder" "unit") ((path.seq i).replace "Inventory" (InvC, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "Inventory" "HTTP_Gateway" "MakeOrder" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_39
    have hP_C : NetworkHasQueue CS_39 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_39, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mInvShipOrder] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans Shipping (st_label.inp "Inventory" "ShipOrder" "unit") ShipA :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mInvShipOrder] (QueueMessage.msg "Inventory" "ShipOrder" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("Shipping", (Shipping, [mInvShipOrder])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_39])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "Shipping" "Inventory" "ShipOrder" "unit") ((path.seq i).replace "Shipping" (ShipA, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "Shipping" "Inventory" "ShipOrder" "unit" ⟨_, hTr⟩
  · -- CS_40
    have hP_C : NetworkHasQueue CS_40 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_40, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGValidCC] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans StConfTp (st_label.inp "HTTP_Gateway" "ValidCC" "unit") SessionType.tEnd :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mHGValidCC] (QueueMessage.msg "HTTP_Gateway" "ValidCC" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("ExternalClient", (StConfTp, [mHGValidCC])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_40])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit") ((path.seq i).replace "ExternalClient" (SessionType.tEnd, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "ExternalClient" "HTTP_Gateway" "ValidCC" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_41
    have hP_C : NetworkHasQueue CS_41 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_41, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGMakeOrder] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans InvB (st_label.inp "HTTP_Gateway" "MakeOrder" "unit") InvC :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mHGMakeOrder] (QueueMessage.msg "HTTP_Gateway" "MakeOrder" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("Inventory", (InvB, [mHGMakeOrder])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_41])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "Inventory" "HTTP_Gateway" "MakeOrder" "unit") ((path.seq i).replace "Inventory" (InvC, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "Inventory" "HTTP_Gateway" "MakeOrder" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_42
    have hP_C : NetworkHasQueue CS_42 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_42, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGMakeCharge] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans PayTa (st_label.inp "HTTP_Gateway" "MakeCharge" "unit") PayIBank :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mHGMakeCharge] (QueueMessage.msg "HTTP_Gateway" "MakeCharge" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("Payment", (PayTa, [mHGMakeCharge])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_42])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "Payment" "HTTP_Gateway" "MakeCharge" "unit") ((path.seq i).replace "Payment" (PayIBank, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "Payment" "HTTP_Gateway" "MakeCharge" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_43
    have hP_C : NetworkHasQueue CS_43 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_43, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGValidCC] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans StConfTp (st_label.inp "HTTP_Gateway" "ValidCC" "unit") SessionType.tEnd :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mHGValidCC] (QueueMessage.msg "HTTP_Gateway" "ValidCC" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("ExternalClient", (StConfTp, [mHGValidCC])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_43])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit") ((path.seq i).replace "ExternalClient" (SessionType.tEnd, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "ExternalClient" "HTTP_Gateway" "ValidCC" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGMakeCharge] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans PayTa (st_label.inp "HTTP_Gateway" "MakeCharge" "unit") PayIBank :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mHGMakeCharge] (QueueMessage.msg "HTTP_Gateway" "MakeCharge" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("Payment", (PayTa, [mHGMakeCharge])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_43])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "Payment" "HTTP_Gateway" "MakeCharge" "unit") ((path.seq i).replace "Payment" (PayIBank, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "Payment" "HTTP_Gateway" "MakeCharge" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mInvShipOrder] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans Shipping (st_label.inp "Inventory" "ShipOrder" "unit") ShipA :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mInvShipOrder] (QueueMessage.msg "Inventory" "ShipOrder" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("Shipping", (Shipping, [mInvShipOrder])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_43])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "Shipping" "Inventory" "ShipOrder" "unit") ((path.seq i).replace "Shipping" (ShipA, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "Shipping" "Inventory" "ShipOrder" "unit" ⟨_, hTr⟩
  · -- CS_44
    have hP_C : NetworkHasQueue CS_44 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_44, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGMakeCharge] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans PayTa (st_label.inp "HTTP_Gateway" "MakeCharge" "unit") PayIBank :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mHGMakeCharge] (QueueMessage.msg "HTTP_Gateway" "MakeCharge" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("Payment", (PayTa, [mHGMakeCharge])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_44])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "Payment" "HTTP_Gateway" "MakeCharge" "unit") ((path.seq i).replace "Payment" (PayIBank, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "Payment" "HTTP_Gateway" "MakeCharge" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_45
    have hP_C : NetworkHasQueue CS_45 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_45, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_46
    have hP_C : NetworkHasQueue CS_46 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_46, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGValidCC] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans StConfTp (st_label.inp "HTTP_Gateway" "ValidCC" "unit") SessionType.tEnd :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mHGValidCC] (QueueMessage.msg "HTTP_Gateway" "ValidCC" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("ExternalClient", (StConfTp, [mHGValidCC])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_46])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit") ((path.seq i).replace "ExternalClient" (SessionType.tEnd, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "ExternalClient" "HTTP_Gateway" "ValidCC" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGMakeOrder] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans InvB (st_label.inp "HTTP_Gateway" "MakeOrder" "unit") InvC :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mHGMakeOrder] (QueueMessage.msg "HTTP_Gateway" "MakeOrder" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("Inventory", (InvB, [mHGMakeOrder])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_46])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "Inventory" "HTTP_Gateway" "MakeOrder" "unit") ((path.seq i).replace "Inventory" (InvC, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "Inventory" "HTTP_Gateway" "MakeOrder" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_47
    have hP_C : NetworkHasQueue CS_47 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_47, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mPayMakeCharge] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans Bank (st_label.inp "Payment" "MakeCharge" "unit") SessionType.tEnd :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mPayMakeCharge] (QueueMessage.msg "Payment" "MakeCharge" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("ExternalBank", (Bank, [mPayMakeCharge])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_47])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit") ((path.seq i).replace "ExternalBank" (SessionType.tEnd, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "ExternalBank" "Payment" "MakeCharge" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mInvShipOrder] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans Shipping (st_label.inp "Inventory" "ShipOrder" "unit") ShipA :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mInvShipOrder] (QueueMessage.msg "Inventory" "ShipOrder" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("Shipping", (Shipping, [mInvShipOrder])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_47])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "Shipping" "Inventory" "ShipOrder" "unit") ((path.seq i).replace "Shipping" (ShipA, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "Shipping" "Inventory" "ShipOrder" "unit" ⟨_, hTr⟩
  · -- CS_48
    have hP_C : NetworkHasQueue CS_48 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_48, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mPayMakeCharge] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans Bank (st_label.inp "Payment" "MakeCharge" "unit") SessionType.tEnd :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mPayMakeCharge] (QueueMessage.msg "Payment" "MakeCharge" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("ExternalBank", (Bank, [mPayMakeCharge])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_48])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit") ((path.seq i).replace "ExternalBank" (SessionType.tEnd, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "ExternalBank" "Payment" "MakeCharge" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGValidCC] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans StConfTp (st_label.inp "HTTP_Gateway" "ValidCC" "unit") SessionType.tEnd :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mHGValidCC] (QueueMessage.msg "HTTP_Gateway" "ValidCC" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("ExternalClient", (StConfTp, [mHGValidCC])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_48])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit") ((path.seq i).replace "ExternalClient" (SessionType.tEnd, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "ExternalClient" "HTTP_Gateway" "ValidCC" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_49
    have hP_C : NetworkHasQueue CS_49 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_49, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mPayMakeCharge] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans Bank (st_label.inp "Payment" "MakeCharge" "unit") SessionType.tEnd :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mPayMakeCharge] (QueueMessage.msg "Payment" "MakeCharge" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("ExternalBank", (Bank, [mPayMakeCharge])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_49])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit") ((path.seq i).replace "ExternalBank" (SessionType.tEnd, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "ExternalBank" "Payment" "MakeCharge" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGMakeOrder] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans InvB (st_label.inp "HTTP_Gateway" "MakeOrder" "unit") InvC :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mHGMakeOrder] (QueueMessage.msg "HTTP_Gateway" "MakeOrder" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("Inventory", (InvB, [mHGMakeOrder])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_49])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "Inventory" "HTTP_Gateway" "MakeOrder" "unit") ((path.seq i).replace "Inventory" (InvC, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "Inventory" "HTTP_Gateway" "MakeOrder" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_50
    have hP_C : NetworkHasQueue CS_50 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_50, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_51
    have hP_C : NetworkHasQueue CS_51 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_51, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGValidCC] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans StConfTp (st_label.inp "HTTP_Gateway" "ValidCC" "unit") SessionType.tEnd :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mHGValidCC] (QueueMessage.msg "HTTP_Gateway" "ValidCC" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("ExternalClient", (StConfTp, [mHGValidCC])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_51])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit") ((path.seq i).replace "ExternalClient" (SessionType.tEnd, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "ExternalClient" "HTTP_Gateway" "ValidCC" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mInvShipOrder] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans Shipping (st_label.inp "Inventory" "ShipOrder" "unit") ShipA :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mInvShipOrder] (QueueMessage.msg "Inventory" "ShipOrder" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("Shipping", (Shipping, [mInvShipOrder])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_51])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "Shipping" "Inventory" "ShipOrder" "unit") ((path.seq i).replace "Shipping" (ShipA, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "Shipping" "Inventory" "ShipOrder" "unit" ⟨_, hTr⟩
  · -- CS_52
    have hP_C : NetworkHasQueue CS_52 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_52, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_53
    have hP_C : NetworkHasQueue CS_53 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_53, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mShipSendEmail] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans Email (st_label.inp "Shipping" "SendOrderShippedEmail" "unit") EmailA :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mShipSendEmail] (QueueMessage.msg "Shipping" "SendOrderShippedEmail" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("ExternalMailserver", (Email, [mShipSendEmail])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_53])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "ExternalMailserver" "Shipping" "SendOrderShippedEmail" "unit") ((path.seq i).replace "ExternalMailserver" (EmailA, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "ExternalMailserver" "Shipping" "SendOrderShippedEmail" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGMakeCharge] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans PayTa (st_label.inp "HTTP_Gateway" "MakeCharge" "unit") PayIBank :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mHGMakeCharge] (QueueMessage.msg "HTTP_Gateway" "MakeCharge" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("Payment", (PayTa, [mHGMakeCharge])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_53])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "Payment" "HTTP_Gateway" "MakeCharge" "unit") ((path.seq i).replace "Payment" (PayIBank, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "Payment" "HTTP_Gateway" "MakeCharge" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_54
    have hP_C : NetworkHasQueue CS_54 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_54, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGValidCC] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans StConfTp (st_label.inp "HTTP_Gateway" "ValidCC" "unit") SessionType.tEnd :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mHGValidCC] (QueueMessage.msg "HTTP_Gateway" "ValidCC" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("ExternalClient", (StConfTp, [mHGValidCC])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_54])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit") ((path.seq i).replace "ExternalClient" (SessionType.tEnd, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "ExternalClient" "HTTP_Gateway" "ValidCC" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGMakeCharge] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans PayTa (st_label.inp "HTTP_Gateway" "MakeCharge" "unit") PayIBank :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mHGMakeCharge] (QueueMessage.msg "HTTP_Gateway" "MakeCharge" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("Payment", (PayTa, [mHGMakeCharge])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_54])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "Payment" "HTTP_Gateway" "MakeCharge" "unit") ((path.seq i).replace "Payment" (PayIBank, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "Payment" "HTTP_Gateway" "MakeCharge" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_55
    have hP_C : NetworkHasQueue CS_55 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_55, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGMakeCharge] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans PayTa (st_label.inp "HTTP_Gateway" "MakeCharge" "unit") PayIBank :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mHGMakeCharge] (QueueMessage.msg "HTTP_Gateway" "MakeCharge" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("Payment", (PayTa, [mHGMakeCharge])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_55])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "Payment" "HTTP_Gateway" "MakeCharge" "unit") ((path.seq i).replace "Payment" (PayIBank, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "Payment" "HTTP_Gateway" "MakeCharge" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mInvShipOrder] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans Shipping (st_label.inp "Inventory" "ShipOrder" "unit") ShipA :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mInvShipOrder] (QueueMessage.msg "Inventory" "ShipOrder" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("Shipping", (Shipping, [mInvShipOrder])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_55])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "Shipping" "Inventory" "ShipOrder" "unit") ((path.seq i).replace "Shipping" (ShipA, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "Shipping" "Inventory" "ShipOrder" "unit" ⟨_, hTr⟩
  · -- CS_56
    have hP_C : NetworkHasQueue CS_56 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_56, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mInvShipOrder] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans Shipping (st_label.inp "Inventory" "ShipOrder" "unit") ShipA :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mInvShipOrder] (QueueMessage.msg "Inventory" "ShipOrder" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("Shipping", (Shipping, [mInvShipOrder])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_56])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "Shipping" "Inventory" "ShipOrder" "unit") ((path.seq i).replace "Shipping" (ShipA, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "Shipping" "Inventory" "ShipOrder" "unit" ⟨_, hTr⟩
  · -- CS_57
    have hP_C : NetworkHasQueue CS_57 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_57, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGValidCC] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans StConfTp (st_label.inp "HTTP_Gateway" "ValidCC" "unit") SessionType.tEnd :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mHGValidCC] (QueueMessage.msg "HTTP_Gateway" "ValidCC" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("ExternalClient", (StConfTp, [mHGValidCC])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_57])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit") ((path.seq i).replace "ExternalClient" (SessionType.tEnd, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "ExternalClient" "HTTP_Gateway" "ValidCC" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_58
    have hP_C : NetworkHasQueue CS_58 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_58, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGMakeOrder] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans InvB (st_label.inp "HTTP_Gateway" "MakeOrder" "unit") InvC :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mHGMakeOrder] (QueueMessage.msg "HTTP_Gateway" "MakeOrder" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("Inventory", (InvB, [mHGMakeOrder])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_58])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "Inventory" "HTTP_Gateway" "MakeOrder" "unit") ((path.seq i).replace "Inventory" (InvC, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "Inventory" "HTTP_Gateway" "MakeOrder" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_59
    have hP_C : NetworkHasQueue CS_59 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_59, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mPayMakeCharge] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans Bank (st_label.inp "Payment" "MakeCharge" "unit") SessionType.tEnd :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mPayMakeCharge] (QueueMessage.msg "Payment" "MakeCharge" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("ExternalBank", (Bank, [mPayMakeCharge])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_59])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit") ((path.seq i).replace "ExternalBank" (SessionType.tEnd, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "ExternalBank" "Payment" "MakeCharge" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_60
    have hP_C : NetworkHasQueue CS_60 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_60, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mPayMakeCharge] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans Bank (st_label.inp "Payment" "MakeCharge" "unit") SessionType.tEnd :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mPayMakeCharge] (QueueMessage.msg "Payment" "MakeCharge" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("ExternalBank", (Bank, [mPayMakeCharge])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_60])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit") ((path.seq i).replace "ExternalBank" (SessionType.tEnd, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "ExternalBank" "Payment" "MakeCharge" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGValidCC] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans StConfTp (st_label.inp "HTTP_Gateway" "ValidCC" "unit") SessionType.tEnd :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mHGValidCC] (QueueMessage.msg "HTTP_Gateway" "ValidCC" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("ExternalClient", (StConfTp, [mHGValidCC])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_60])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit") ((path.seq i).replace "ExternalClient" (SessionType.tEnd, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "ExternalClient" "HTTP_Gateway" "ValidCC" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mInvShipOrder] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans Shipping (st_label.inp "Inventory" "ShipOrder" "unit") ShipA :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mInvShipOrder] (QueueMessage.msg "Inventory" "ShipOrder" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("Shipping", (Shipping, [mInvShipOrder])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_60])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "Shipping" "Inventory" "ShipOrder" "unit") ((path.seq i).replace "Shipping" (ShipA, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "Shipping" "Inventory" "ShipOrder" "unit" ⟨_, hTr⟩
  · -- CS_61
    have hP_C : NetworkHasQueue CS_61 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_61, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mPayMakeCharge] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans Bank (st_label.inp "Payment" "MakeCharge" "unit") SessionType.tEnd :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mPayMakeCharge] (QueueMessage.msg "Payment" "MakeCharge" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("ExternalBank", (Bank, [mPayMakeCharge])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_61])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit") ((path.seq i).replace "ExternalBank" (SessionType.tEnd, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "ExternalBank" "Payment" "MakeCharge" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_62
    have hP_C : NetworkHasQueue CS_62 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_62, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mShipSendEmail] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans Email (st_label.inp "Shipping" "SendOrderShippedEmail" "unit") EmailA :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mShipSendEmail] (QueueMessage.msg "Shipping" "SendOrderShippedEmail" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("ExternalMailserver", (Email, [mShipSendEmail])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_62])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "ExternalMailserver" "Shipping" "SendOrderShippedEmail" "unit") ((path.seq i).replace "ExternalMailserver" (EmailA, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "ExternalMailserver" "Shipping" "SendOrderShippedEmail" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_63
    have hP_C : NetworkHasQueue CS_63 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_63, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGValidCC] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans StConfTp (st_label.inp "HTTP_Gateway" "ValidCC" "unit") SessionType.tEnd :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mHGValidCC] (QueueMessage.msg "HTTP_Gateway" "ValidCC" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("ExternalClient", (StConfTp, [mHGValidCC])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_63])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit") ((path.seq i).replace "ExternalClient" (SessionType.tEnd, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "ExternalClient" "HTTP_Gateway" "ValidCC" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_64
    have hP_C : NetworkHasQueue CS_64 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_64, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mInvShipOrder] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans Shipping (st_label.inp "Inventory" "ShipOrder" "unit") ShipA :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mInvShipOrder] (QueueMessage.msg "Inventory" "ShipOrder" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("Shipping", (Shipping, [mInvShipOrder])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_64])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "Shipping" "Inventory" "ShipOrder" "unit") ((path.seq i).replace "Shipping" (ShipA, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "Shipping" "Inventory" "ShipOrder" "unit" ⟨_, hTr⟩
  · -- CS_65
    have hP_C : NetworkHasQueue CS_65 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_65, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGMakeCharge] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans PayTa (st_label.inp "HTTP_Gateway" "MakeCharge" "unit") PayIBank :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mHGMakeCharge] (QueueMessage.msg "HTTP_Gateway" "MakeCharge" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("Payment", (PayTa, [mHGMakeCharge])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_65])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "Payment" "HTTP_Gateway" "MakeCharge" "unit") ((path.seq i).replace "Payment" (PayIBank, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "Payment" "HTTP_Gateway" "MakeCharge" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_66
    have hP_C : NetworkHasQueue CS_66 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_66, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGValidCC] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans StConfTp (st_label.inp "HTTP_Gateway" "ValidCC" "unit") SessionType.tEnd :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mHGValidCC] (QueueMessage.msg "HTTP_Gateway" "ValidCC" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("ExternalClient", (StConfTp, [mHGValidCC])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_66])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit") ((path.seq i).replace "ExternalClient" (SessionType.tEnd, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "ExternalClient" "HTTP_Gateway" "ValidCC" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mShipSendEmail] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans Email (st_label.inp "Shipping" "SendOrderShippedEmail" "unit") EmailA :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mShipSendEmail] (QueueMessage.msg "Shipping" "SendOrderShippedEmail" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("ExternalMailserver", (Email, [mShipSendEmail])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_66])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "ExternalMailserver" "Shipping" "SendOrderShippedEmail" "unit") ((path.seq i).replace "ExternalMailserver" (EmailA, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "ExternalMailserver" "Shipping" "SendOrderShippedEmail" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGMakeCharge] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans PayTa (st_label.inp "HTTP_Gateway" "MakeCharge" "unit") PayIBank :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mHGMakeCharge] (QueueMessage.msg "HTTP_Gateway" "MakeCharge" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("Payment", (PayTa, [mHGMakeCharge])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_66])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "Payment" "HTTP_Gateway" "MakeCharge" "unit") ((path.seq i).replace "Payment" (PayIBank, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "Payment" "HTTP_Gateway" "MakeCharge" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_67
    have hP_C : NetworkHasQueue CS_67 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_67, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGMakeCharge] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans PayTa (st_label.inp "HTTP_Gateway" "MakeCharge" "unit") PayIBank :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mHGMakeCharge] (QueueMessage.msg "HTTP_Gateway" "MakeCharge" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("Payment", (PayTa, [mHGMakeCharge])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_67])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "Payment" "HTTP_Gateway" "MakeCharge" "unit") ((path.seq i).replace "Payment" (PayIBank, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "Payment" "HTTP_Gateway" "MakeCharge" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_68
    have hP_C : NetworkHasQueue CS_68 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_68, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_69
    have hP_C : NetworkHasQueue CS_69 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_69, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGValidCC] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans StConfTp (st_label.inp "HTTP_Gateway" "ValidCC" "unit") SessionType.tEnd :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mHGValidCC] (QueueMessage.msg "HTTP_Gateway" "ValidCC" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("ExternalClient", (StConfTp, [mHGValidCC])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_69])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit") ((path.seq i).replace "ExternalClient" (SessionType.tEnd, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "ExternalClient" "HTTP_Gateway" "ValidCC" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mInvShipOrder] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans Shipping (st_label.inp "Inventory" "ShipOrder" "unit") ShipA :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mInvShipOrder] (QueueMessage.msg "Inventory" "ShipOrder" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("Shipping", (Shipping, [mInvShipOrder])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_69])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "Shipping" "Inventory" "ShipOrder" "unit") ((path.seq i).replace "Shipping" (ShipA, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "Shipping" "Inventory" "ShipOrder" "unit" ⟨_, hTr⟩
  · -- CS_70
    have hP_C : NetworkHasQueue CS_70 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_70, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_71
    have hP_C : NetworkHasQueue CS_71 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_71, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mPayMakeCharge] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans Bank (st_label.inp "Payment" "MakeCharge" "unit") SessionType.tEnd :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mPayMakeCharge] (QueueMessage.msg "Payment" "MakeCharge" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("ExternalBank", (Bank, [mPayMakeCharge])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_71])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit") ((path.seq i).replace "ExternalBank" (SessionType.tEnd, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "ExternalBank" "Payment" "MakeCharge" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mShipSendEmail] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans Email (st_label.inp "Shipping" "SendOrderShippedEmail" "unit") EmailA :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mShipSendEmail] (QueueMessage.msg "Shipping" "SendOrderShippedEmail" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("ExternalMailserver", (Email, [mShipSendEmail])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_71])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "ExternalMailserver" "Shipping" "SendOrderShippedEmail" "unit") ((path.seq i).replace "ExternalMailserver" (EmailA, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "ExternalMailserver" "Shipping" "SendOrderShippedEmail" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_72
    have hP_C : NetworkHasQueue CS_72 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_72, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mPayMakeCharge] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans Bank (st_label.inp "Payment" "MakeCharge" "unit") SessionType.tEnd :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mPayMakeCharge] (QueueMessage.msg "Payment" "MakeCharge" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("ExternalBank", (Bank, [mPayMakeCharge])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_72])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit") ((path.seq i).replace "ExternalBank" (SessionType.tEnd, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "ExternalBank" "Payment" "MakeCharge" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGValidCC] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans StConfTp (st_label.inp "HTTP_Gateway" "ValidCC" "unit") SessionType.tEnd :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mHGValidCC] (QueueMessage.msg "HTTP_Gateway" "ValidCC" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("ExternalClient", (StConfTp, [mHGValidCC])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_72])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit") ((path.seq i).replace "ExternalClient" (SessionType.tEnd, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "ExternalClient" "HTTP_Gateway" "ValidCC" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_73
    have hP_C : NetworkHasQueue CS_73 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_73, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mPayMakeCharge] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans Bank (st_label.inp "Payment" "MakeCharge" "unit") SessionType.tEnd :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mPayMakeCharge] (QueueMessage.msg "Payment" "MakeCharge" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("ExternalBank", (Bank, [mPayMakeCharge])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_73])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit") ((path.seq i).replace "ExternalBank" (SessionType.tEnd, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "ExternalBank" "Payment" "MakeCharge" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mInvShipOrder] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans Shipping (st_label.inp "Inventory" "ShipOrder" "unit") ShipA :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mInvShipOrder] (QueueMessage.msg "Inventory" "ShipOrder" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("Shipping", (Shipping, [mInvShipOrder])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_73])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "Shipping" "Inventory" "ShipOrder" "unit") ((path.seq i).replace "Shipping" (ShipA, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "Shipping" "Inventory" "ShipOrder" "unit" ⟨_, hTr⟩
  · -- CS_74
    have hP_C : NetworkHasQueue CS_74 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_74, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_75
    have hP_C : NetworkHasQueue CS_75 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_75, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGValidCC] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans StConfTp (st_label.inp "HTTP_Gateway" "ValidCC" "unit") SessionType.tEnd :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mHGValidCC] (QueueMessage.msg "HTTP_Gateway" "ValidCC" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("ExternalClient", (StConfTp, [mHGValidCC])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_75])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit") ((path.seq i).replace "ExternalClient" (SessionType.tEnd, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "ExternalClient" "HTTP_Gateway" "ValidCC" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mShipSendEmail] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans Email (st_label.inp "Shipping" "SendOrderShippedEmail" "unit") EmailA :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mShipSendEmail] (QueueMessage.msg "Shipping" "SendOrderShippedEmail" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("ExternalMailserver", (Email, [mShipSendEmail])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_75])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "ExternalMailserver" "Shipping" "SendOrderShippedEmail" "unit") ((path.seq i).replace "ExternalMailserver" (EmailA, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "ExternalMailserver" "Shipping" "SendOrderShippedEmail" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_76
    have hP_C : NetworkHasQueue CS_76 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_76, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_77
    have hP_C : NetworkHasQueue CS_77 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_77, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGMakeCharge] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans PayTa (st_label.inp "HTTP_Gateway" "MakeCharge" "unit") PayIBank :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mHGMakeCharge] (QueueMessage.msg "HTTP_Gateway" "MakeCharge" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("Payment", (PayTa, [mHGMakeCharge])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_77])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "Payment" "HTTP_Gateway" "MakeCharge" "unit") ((path.seq i).replace "Payment" (PayIBank, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "Payment" "HTTP_Gateway" "MakeCharge" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mEMSuccess] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans ShipB (st_label.inp "ExternalMailserver" "Success" "unit") SessionType.tEnd :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mEMSuccess] (QueueMessage.msg "ExternalMailserver" "Success" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("Shipping", (ShipB, [mEMSuccess])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_77])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "Shipping" "ExternalMailserver" "Success" "unit") ((path.seq i).replace "Shipping" (SessionType.tEnd, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "Shipping" "ExternalMailserver" "Success" "unit" ⟨_, hTr⟩
  · -- CS_78
    have hP_C : NetworkHasQueue CS_78 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_78, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGValidCC] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans StConfTp (st_label.inp "HTTP_Gateway" "ValidCC" "unit") SessionType.tEnd :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mHGValidCC] (QueueMessage.msg "HTTP_Gateway" "ValidCC" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("ExternalClient", (StConfTp, [mHGValidCC])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_78])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit") ((path.seq i).replace "ExternalClient" (SessionType.tEnd, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "ExternalClient" "HTTP_Gateway" "ValidCC" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGMakeCharge] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans PayTa (st_label.inp "HTTP_Gateway" "MakeCharge" "unit") PayIBank :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mHGMakeCharge] (QueueMessage.msg "HTTP_Gateway" "MakeCharge" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("Payment", (PayTa, [mHGMakeCharge])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_78])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "Payment" "HTTP_Gateway" "MakeCharge" "unit") ((path.seq i).replace "Payment" (PayIBank, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "Payment" "HTTP_Gateway" "MakeCharge" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_79
    have hP_C : NetworkHasQueue CS_79 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_79, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mShipSendEmail] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans Email (st_label.inp "Shipping" "SendOrderShippedEmail" "unit") EmailA :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mShipSendEmail] (QueueMessage.msg "Shipping" "SendOrderShippedEmail" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("ExternalMailserver", (Email, [mShipSendEmail])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_79])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "ExternalMailserver" "Shipping" "SendOrderShippedEmail" "unit") ((path.seq i).replace "ExternalMailserver" (EmailA, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "ExternalMailserver" "Shipping" "SendOrderShippedEmail" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGMakeCharge] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans PayTa (st_label.inp "HTTP_Gateway" "MakeCharge" "unit") PayIBank :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mHGMakeCharge] (QueueMessage.msg "HTTP_Gateway" "MakeCharge" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("Payment", (PayTa, [mHGMakeCharge])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_79])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "Payment" "HTTP_Gateway" "MakeCharge" "unit") ((path.seq i).replace "Payment" (PayIBank, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "Payment" "HTTP_Gateway" "MakeCharge" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_80
    have hP_C : NetworkHasQueue CS_80 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_80, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mShipSendEmail] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans Email (st_label.inp "Shipping" "SendOrderShippedEmail" "unit") EmailA :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mShipSendEmail] (QueueMessage.msg "Shipping" "SendOrderShippedEmail" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("ExternalMailserver", (Email, [mShipSendEmail])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_80])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "ExternalMailserver" "Shipping" "SendOrderShippedEmail" "unit") ((path.seq i).replace "ExternalMailserver" (EmailA, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "ExternalMailserver" "Shipping" "SendOrderShippedEmail" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_81
    have hP_C : NetworkHasQueue CS_81 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_81, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGValidCC] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans StConfTp (st_label.inp "HTTP_Gateway" "ValidCC" "unit") SessionType.tEnd :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mHGValidCC] (QueueMessage.msg "HTTP_Gateway" "ValidCC" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("ExternalClient", (StConfTp, [mHGValidCC])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_81])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit") ((path.seq i).replace "ExternalClient" (SessionType.tEnd, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "ExternalClient" "HTTP_Gateway" "ValidCC" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_82
    have hP_C : NetworkHasQueue CS_82 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_82, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mInvShipOrder] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans Shipping (st_label.inp "Inventory" "ShipOrder" "unit") ShipA :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mInvShipOrder] (QueueMessage.msg "Inventory" "ShipOrder" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("Shipping", (Shipping, [mInvShipOrder])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_82])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "Shipping" "Inventory" "ShipOrder" "unit") ((path.seq i).replace "Shipping" (ShipA, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "Shipping" "Inventory" "ShipOrder" "unit" ⟨_, hTr⟩
  · -- CS_83
    have hP_C : NetworkHasQueue CS_83 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_83, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mPayMakeCharge] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans Bank (st_label.inp "Payment" "MakeCharge" "unit") SessionType.tEnd :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mPayMakeCharge] (QueueMessage.msg "Payment" "MakeCharge" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("ExternalBank", (Bank, [mPayMakeCharge])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_83])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit") ((path.seq i).replace "ExternalBank" (SessionType.tEnd, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "ExternalBank" "Payment" "MakeCharge" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_84
    have hP_C : NetworkHasQueue CS_84 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_84, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mPayMakeCharge] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans Bank (st_label.inp "Payment" "MakeCharge" "unit") SessionType.tEnd :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mPayMakeCharge] (QueueMessage.msg "Payment" "MakeCharge" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("ExternalBank", (Bank, [mPayMakeCharge])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_84])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit") ((path.seq i).replace "ExternalBank" (SessionType.tEnd, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "ExternalBank" "Payment" "MakeCharge" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGValidCC] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans StConfTp (st_label.inp "HTTP_Gateway" "ValidCC" "unit") SessionType.tEnd :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mHGValidCC] (QueueMessage.msg "HTTP_Gateway" "ValidCC" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("ExternalClient", (StConfTp, [mHGValidCC])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_84])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit") ((path.seq i).replace "ExternalClient" (SessionType.tEnd, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "ExternalClient" "HTTP_Gateway" "ValidCC" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mShipSendEmail] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans Email (st_label.inp "Shipping" "SendOrderShippedEmail" "unit") EmailA :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mShipSendEmail] (QueueMessage.msg "Shipping" "SendOrderShippedEmail" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("ExternalMailserver", (Email, [mShipSendEmail])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_84])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "ExternalMailserver" "Shipping" "SendOrderShippedEmail" "unit") ((path.seq i).replace "ExternalMailserver" (EmailA, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "ExternalMailserver" "Shipping" "SendOrderShippedEmail" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_85
    have hP_C : NetworkHasQueue CS_85 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_85, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mPayMakeCharge] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans Bank (st_label.inp "Payment" "MakeCharge" "unit") SessionType.tEnd :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mPayMakeCharge] (QueueMessage.msg "Payment" "MakeCharge" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("ExternalBank", (Bank, [mPayMakeCharge])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_85])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit") ((path.seq i).replace "ExternalBank" (SessionType.tEnd, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "ExternalBank" "Payment" "MakeCharge" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_86
    have hP_C : NetworkHasQueue CS_86 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_86, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mEMSuccess] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans ShipB (st_label.inp "ExternalMailserver" "Success" "unit") SessionType.tEnd :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mEMSuccess] (QueueMessage.msg "ExternalMailserver" "Success" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("Shipping", (ShipB, [mEMSuccess])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_86])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "Shipping" "ExternalMailserver" "Success" "unit") ((path.seq i).replace "Shipping" (SessionType.tEnd, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "Shipping" "ExternalMailserver" "Success" "unit" ⟨_, hTr⟩
  · -- CS_87
    have hP_C : NetworkHasQueue CS_87 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_87, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGValidCC] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans StConfTp (st_label.inp "HTTP_Gateway" "ValidCC" "unit") SessionType.tEnd :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mHGValidCC] (QueueMessage.msg "HTTP_Gateway" "ValidCC" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("ExternalClient", (StConfTp, [mHGValidCC])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_87])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit") ((path.seq i).replace "ExternalClient" (SessionType.tEnd, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "ExternalClient" "HTTP_Gateway" "ValidCC" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_88
    have hP_C : NetworkHasQueue CS_88 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_88, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mShipSendEmail] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans Email (st_label.inp "Shipping" "SendOrderShippedEmail" "unit") EmailA :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mShipSendEmail] (QueueMessage.msg "Shipping" "SendOrderShippedEmail" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("ExternalMailserver", (Email, [mShipSendEmail])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_88])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "ExternalMailserver" "Shipping" "SendOrderShippedEmail" "unit") ((path.seq i).replace "ExternalMailserver" (EmailA, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "ExternalMailserver" "Shipping" "SendOrderShippedEmail" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_89
    have hP_C : NetworkHasQueue CS_89 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_89, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGMakeCharge] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans PayTa (st_label.inp "HTTP_Gateway" "MakeCharge" "unit") PayIBank :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mHGMakeCharge] (QueueMessage.msg "HTTP_Gateway" "MakeCharge" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("Payment", (PayTa, [mHGMakeCharge])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_89])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "Payment" "HTTP_Gateway" "MakeCharge" "unit") ((path.seq i).replace "Payment" (PayIBank, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "Payment" "HTTP_Gateway" "MakeCharge" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_90
    have hP_C : NetworkHasQueue CS_90 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_90, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGValidCC] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans StConfTp (st_label.inp "HTTP_Gateway" "ValidCC" "unit") SessionType.tEnd :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mHGValidCC] (QueueMessage.msg "HTTP_Gateway" "ValidCC" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("ExternalClient", (StConfTp, [mHGValidCC])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_90])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit") ((path.seq i).replace "ExternalClient" (SessionType.tEnd, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "ExternalClient" "HTTP_Gateway" "ValidCC" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGMakeCharge] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans PayTa (st_label.inp "HTTP_Gateway" "MakeCharge" "unit") PayIBank :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mHGMakeCharge] (QueueMessage.msg "HTTP_Gateway" "MakeCharge" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("Payment", (PayTa, [mHGMakeCharge])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_90])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "Payment" "HTTP_Gateway" "MakeCharge" "unit") ((path.seq i).replace "Payment" (PayIBank, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "Payment" "HTTP_Gateway" "MakeCharge" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mEMSuccess] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans ShipB (st_label.inp "ExternalMailserver" "Success" "unit") SessionType.tEnd :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mEMSuccess] (QueueMessage.msg "ExternalMailserver" "Success" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("Shipping", (ShipB, [mEMSuccess])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_90])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "Shipping" "ExternalMailserver" "Success" "unit") ((path.seq i).replace "Shipping" (SessionType.tEnd, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "Shipping" "ExternalMailserver" "Success" "unit" ⟨_, hTr⟩
  · -- CS_91
    have hP_C : NetworkHasQueue CS_91 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_91, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGMakeCharge] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans PayTa (st_label.inp "HTTP_Gateway" "MakeCharge" "unit") PayIBank :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mHGMakeCharge] (QueueMessage.msg "HTTP_Gateway" "MakeCharge" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("Payment", (PayTa, [mHGMakeCharge])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_91])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "Payment" "HTTP_Gateway" "MakeCharge" "unit") ((path.seq i).replace "Payment" (PayIBank, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "Payment" "HTTP_Gateway" "MakeCharge" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_92
    have hP_C : NetworkHasQueue CS_92 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_92, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_93
    have hP_C : NetworkHasQueue CS_93 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_93, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGValidCC] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans StConfTp (st_label.inp "HTTP_Gateway" "ValidCC" "unit") SessionType.tEnd :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mHGValidCC] (QueueMessage.msg "HTTP_Gateway" "ValidCC" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("ExternalClient", (StConfTp, [mHGValidCC])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_93])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit") ((path.seq i).replace "ExternalClient" (SessionType.tEnd, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "ExternalClient" "HTTP_Gateway" "ValidCC" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mShipSendEmail] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans Email (st_label.inp "Shipping" "SendOrderShippedEmail" "unit") EmailA :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mShipSendEmail] (QueueMessage.msg "Shipping" "SendOrderShippedEmail" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("ExternalMailserver", (Email, [mShipSendEmail])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_93])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "ExternalMailserver" "Shipping" "SendOrderShippedEmail" "unit") ((path.seq i).replace "ExternalMailserver" (EmailA, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "ExternalMailserver" "Shipping" "SendOrderShippedEmail" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_94
    have hP_C : NetworkHasQueue CS_94 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_94, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_95
    have hP_C : NetworkHasQueue CS_95 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_95, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mPayMakeCharge] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans Bank (st_label.inp "Payment" "MakeCharge" "unit") SessionType.tEnd :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mPayMakeCharge] (QueueMessage.msg "Payment" "MakeCharge" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("ExternalBank", (Bank, [mPayMakeCharge])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_95])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit") ((path.seq i).replace "ExternalBank" (SessionType.tEnd, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "ExternalBank" "Payment" "MakeCharge" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mEMSuccess] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans ShipB (st_label.inp "ExternalMailserver" "Success" "unit") SessionType.tEnd :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mEMSuccess] (QueueMessage.msg "ExternalMailserver" "Success" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("Shipping", (ShipB, [mEMSuccess])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_95])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "Shipping" "ExternalMailserver" "Success" "unit") ((path.seq i).replace "Shipping" (SessionType.tEnd, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "Shipping" "ExternalMailserver" "Success" "unit" ⟨_, hTr⟩
  · -- CS_96
    have hP_C : NetworkHasQueue CS_96 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_96, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mPayMakeCharge] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans Bank (st_label.inp "Payment" "MakeCharge" "unit") SessionType.tEnd :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mPayMakeCharge] (QueueMessage.msg "Payment" "MakeCharge" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("ExternalBank", (Bank, [mPayMakeCharge])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_96])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit") ((path.seq i).replace "ExternalBank" (SessionType.tEnd, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "ExternalBank" "Payment" "MakeCharge" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGValidCC] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans StConfTp (st_label.inp "HTTP_Gateway" "ValidCC" "unit") SessionType.tEnd :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mHGValidCC] (QueueMessage.msg "HTTP_Gateway" "ValidCC" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("ExternalClient", (StConfTp, [mHGValidCC])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_96])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit") ((path.seq i).replace "ExternalClient" (SessionType.tEnd, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "ExternalClient" "HTTP_Gateway" "ValidCC" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_97
    have hP_C : NetworkHasQueue CS_97 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_97, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mPayMakeCharge] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans Bank (st_label.inp "Payment" "MakeCharge" "unit") SessionType.tEnd :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mPayMakeCharge] (QueueMessage.msg "Payment" "MakeCharge" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("ExternalBank", (Bank, [mPayMakeCharge])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_97])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit") ((path.seq i).replace "ExternalBank" (SessionType.tEnd, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "ExternalBank" "Payment" "MakeCharge" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mShipSendEmail] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans Email (st_label.inp "Shipping" "SendOrderShippedEmail" "unit") EmailA :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mShipSendEmail] (QueueMessage.msg "Shipping" "SendOrderShippedEmail" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("ExternalMailserver", (Email, [mShipSendEmail])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_97])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "ExternalMailserver" "Shipping" "SendOrderShippedEmail" "unit") ((path.seq i).replace "ExternalMailserver" (EmailA, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "ExternalMailserver" "Shipping" "SendOrderShippedEmail" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_98
    have hP_C : NetworkHasQueue CS_98 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_98, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_99
    have hP_C : NetworkHasQueue CS_99 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_99, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGValidCC] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans StConfTp (st_label.inp "HTTP_Gateway" "ValidCC" "unit") SessionType.tEnd :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mHGValidCC] (QueueMessage.msg "HTTP_Gateway" "ValidCC" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("ExternalClient", (StConfTp, [mHGValidCC])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_99])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit") ((path.seq i).replace "ExternalClient" (SessionType.tEnd, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "ExternalClient" "HTTP_Gateway" "ValidCC" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mEMSuccess] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans ShipB (st_label.inp "ExternalMailserver" "Success" "unit") SessionType.tEnd :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mEMSuccess] (QueueMessage.msg "ExternalMailserver" "Success" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("Shipping", (ShipB, [mEMSuccess])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_99])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "Shipping" "ExternalMailserver" "Success" "unit") ((path.seq i).replace "Shipping" (SessionType.tEnd, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "Shipping" "ExternalMailserver" "Success" "unit" ⟨_, hTr⟩
  · -- CS_100
    have hP_C : NetworkHasQueue CS_100 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_100, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_101
    have hP_C : NetworkHasQueue CS_101 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_101, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGValidCC] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans StConfTp (st_label.inp "HTTP_Gateway" "ValidCC" "unit") SessionType.tEnd :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mHGValidCC] (QueueMessage.msg "HTTP_Gateway" "ValidCC" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("ExternalClient", (StConfTp, [mHGValidCC])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_101])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit") ((path.seq i).replace "ExternalClient" (SessionType.tEnd, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "ExternalClient" "HTTP_Gateway" "ValidCC" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGMakeCharge] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans PayTa (st_label.inp "HTTP_Gateway" "MakeCharge" "unit") PayIBank :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mHGMakeCharge] (QueueMessage.msg "HTTP_Gateway" "MakeCharge" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("Payment", (PayTa, [mHGMakeCharge])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_101])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "Payment" "HTTP_Gateway" "MakeCharge" "unit") ((path.seq i).replace "Payment" (PayIBank, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "Payment" "HTTP_Gateway" "MakeCharge" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_102
    have hP_C : NetworkHasQueue CS_102 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_102, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGMakeCharge] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans PayTa (st_label.inp "HTTP_Gateway" "MakeCharge" "unit") PayIBank :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mHGMakeCharge] (QueueMessage.msg "HTTP_Gateway" "MakeCharge" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("Payment", (PayTa, [mHGMakeCharge])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_102])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "Payment" "HTTP_Gateway" "MakeCharge" "unit") ((path.seq i).replace "Payment" (PayIBank, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "Payment" "HTTP_Gateway" "MakeCharge" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mEMSuccess] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans ShipB (st_label.inp "ExternalMailserver" "Success" "unit") SessionType.tEnd :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mEMSuccess] (QueueMessage.msg "ExternalMailserver" "Success" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("Shipping", (ShipB, [mEMSuccess])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_102])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "Shipping" "ExternalMailserver" "Success" "unit") ((path.seq i).replace "Shipping" (SessionType.tEnd, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "Shipping" "ExternalMailserver" "Success" "unit" ⟨_, hTr⟩
  · -- CS_103
    have hP_C : NetworkHasQueue CS_103 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_103, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mEMSuccess] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans ShipB (st_label.inp "ExternalMailserver" "Success" "unit") SessionType.tEnd :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mEMSuccess] (QueueMessage.msg "ExternalMailserver" "Success" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("Shipping", (ShipB, [mEMSuccess])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_103])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "Shipping" "ExternalMailserver" "Success" "unit") ((path.seq i).replace "Shipping" (SessionType.tEnd, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "Shipping" "ExternalMailserver" "Success" "unit" ⟨_, hTr⟩
  · -- CS_104
    have hP_C : NetworkHasQueue CS_104 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_104, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGValidCC] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans StConfTp (st_label.inp "HTTP_Gateway" "ValidCC" "unit") SessionType.tEnd :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mHGValidCC] (QueueMessage.msg "HTTP_Gateway" "ValidCC" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("ExternalClient", (StConfTp, [mHGValidCC])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_104])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit") ((path.seq i).replace "ExternalClient" (SessionType.tEnd, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "ExternalClient" "HTTP_Gateway" "ValidCC" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_105
    have hP_C : NetworkHasQueue CS_105 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_105, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mShipSendEmail] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans Email (st_label.inp "Shipping" "SendOrderShippedEmail" "unit") EmailA :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mShipSendEmail] (QueueMessage.msg "Shipping" "SendOrderShippedEmail" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("ExternalMailserver", (Email, [mShipSendEmail])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_105])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "ExternalMailserver" "Shipping" "SendOrderShippedEmail" "unit") ((path.seq i).replace "ExternalMailserver" (EmailA, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "ExternalMailserver" "Shipping" "SendOrderShippedEmail" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_106
    have hP_C : NetworkHasQueue CS_106 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_106, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mPayMakeCharge] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans Bank (st_label.inp "Payment" "MakeCharge" "unit") SessionType.tEnd :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mPayMakeCharge] (QueueMessage.msg "Payment" "MakeCharge" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("ExternalBank", (Bank, [mPayMakeCharge])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_106])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit") ((path.seq i).replace "ExternalBank" (SessionType.tEnd, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "ExternalBank" "Payment" "MakeCharge" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_107
    have hP_C : NetworkHasQueue CS_107 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_107, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mPayMakeCharge] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans Bank (st_label.inp "Payment" "MakeCharge" "unit") SessionType.tEnd :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mPayMakeCharge] (QueueMessage.msg "Payment" "MakeCharge" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("ExternalBank", (Bank, [mPayMakeCharge])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_107])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit") ((path.seq i).replace "ExternalBank" (SessionType.tEnd, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "ExternalBank" "Payment" "MakeCharge" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGValidCC] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans StConfTp (st_label.inp "HTTP_Gateway" "ValidCC" "unit") SessionType.tEnd :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mHGValidCC] (QueueMessage.msg "HTTP_Gateway" "ValidCC" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("ExternalClient", (StConfTp, [mHGValidCC])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_107])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit") ((path.seq i).replace "ExternalClient" (SessionType.tEnd, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "ExternalClient" "HTTP_Gateway" "ValidCC" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mEMSuccess] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans ShipB (st_label.inp "ExternalMailserver" "Success" "unit") SessionType.tEnd :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mEMSuccess] (QueueMessage.msg "ExternalMailserver" "Success" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("Shipping", (ShipB, [mEMSuccess])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_107])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "Shipping" "ExternalMailserver" "Success" "unit") ((path.seq i).replace "Shipping" (SessionType.tEnd, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "Shipping" "ExternalMailserver" "Success" "unit" ⟨_, hTr⟩
  · -- CS_108
    have hP_C : NetworkHasQueue CS_108 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_108, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mPayMakeCharge] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans Bank (st_label.inp "Payment" "MakeCharge" "unit") SessionType.tEnd :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mPayMakeCharge] (QueueMessage.msg "Payment" "MakeCharge" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("ExternalBank", (Bank, [mPayMakeCharge])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_108])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit") ((path.seq i).replace "ExternalBank" (SessionType.tEnd, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "ExternalBank" "Payment" "MakeCharge" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_109
    have hP_C : NetworkHasQueue CS_109 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_109, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGValidCC] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans StConfTp (st_label.inp "HTTP_Gateway" "ValidCC" "unit") SessionType.tEnd :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mHGValidCC] (QueueMessage.msg "HTTP_Gateway" "ValidCC" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("ExternalClient", (StConfTp, [mHGValidCC])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_109])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit") ((path.seq i).replace "ExternalClient" (SessionType.tEnd, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "ExternalClient" "HTTP_Gateway" "ValidCC" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_110
    have hP_C : NetworkHasQueue CS_110 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_110, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mEMSuccess] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans ShipB (st_label.inp "ExternalMailserver" "Success" "unit") SessionType.tEnd :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mEMSuccess] (QueueMessage.msg "ExternalMailserver" "Success" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("Shipping", (ShipB, [mEMSuccess])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_110])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "Shipping" "ExternalMailserver" "Success" "unit") ((path.seq i).replace "Shipping" (SessionType.tEnd, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "Shipping" "ExternalMailserver" "Success" "unit" ⟨_, hTr⟩
  · -- CS_111
    have hP_C : NetworkHasQueue CS_111 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_111, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGMakeCharge] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans PayTa (st_label.inp "HTTP_Gateway" "MakeCharge" "unit") PayIBank :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mHGMakeCharge] (QueueMessage.msg "HTTP_Gateway" "MakeCharge" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("Payment", (PayTa, [mHGMakeCharge])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_111])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "Payment" "HTTP_Gateway" "MakeCharge" "unit") ((path.seq i).replace "Payment" (PayIBank, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "Payment" "HTTP_Gateway" "MakeCharge" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_112
    have hP_C : NetworkHasQueue CS_112 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_112, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_113
    have hP_C : NetworkHasQueue CS_113 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_113, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGValidCC] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans StConfTp (st_label.inp "HTTP_Gateway" "ValidCC" "unit") SessionType.tEnd :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mHGValidCC] (QueueMessage.msg "HTTP_Gateway" "ValidCC" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("ExternalClient", (StConfTp, [mHGValidCC])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_113])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit") ((path.seq i).replace "ExternalClient" (SessionType.tEnd, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "ExternalClient" "HTTP_Gateway" "ValidCC" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mEMSuccess] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans ShipB (st_label.inp "ExternalMailserver" "Success" "unit") SessionType.tEnd :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mEMSuccess] (QueueMessage.msg "ExternalMailserver" "Success" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("Shipping", (ShipB, [mEMSuccess])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_113])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "Shipping" "ExternalMailserver" "Success" "unit") ((path.seq i).replace "Shipping" (SessionType.tEnd, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "Shipping" "ExternalMailserver" "Success" "unit" ⟨_, hTr⟩
  · -- CS_114
    have hP_C : NetworkHasQueue CS_114 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_114, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_115
    have hP_C : NetworkHasQueue CS_115 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_115, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mPayMakeCharge] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans Bank (st_label.inp "Payment" "MakeCharge" "unit") SessionType.tEnd :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mPayMakeCharge] (QueueMessage.msg "Payment" "MakeCharge" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("ExternalBank", (Bank, [mPayMakeCharge])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_115])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit") ((path.seq i).replace "ExternalBank" (SessionType.tEnd, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "ExternalBank" "Payment" "MakeCharge" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGValidCC] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans StConfTp (st_label.inp "HTTP_Gateway" "ValidCC" "unit") SessionType.tEnd :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mHGValidCC] (QueueMessage.msg "HTTP_Gateway" "ValidCC" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("ExternalClient", (StConfTp, [mHGValidCC])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_115])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit") ((path.seq i).replace "ExternalClient" (SessionType.tEnd, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "ExternalClient" "HTTP_Gateway" "ValidCC" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_116
    have hP_C : NetworkHasQueue CS_116 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_116, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mPayMakeCharge] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans Bank (st_label.inp "Payment" "MakeCharge" "unit") SessionType.tEnd :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mPayMakeCharge] (QueueMessage.msg "Payment" "MakeCharge" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("ExternalBank", (Bank, [mPayMakeCharge])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_116])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit") ((path.seq i).replace "ExternalBank" (SessionType.tEnd, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "ExternalBank" "Payment" "MakeCharge" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mEMSuccess] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans ShipB (st_label.inp "ExternalMailserver" "Success" "unit") SessionType.tEnd :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mEMSuccess] (QueueMessage.msg "ExternalMailserver" "Success" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("Shipping", (ShipB, [mEMSuccess])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_116])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "Shipping" "ExternalMailserver" "Success" "unit") ((path.seq i).replace "Shipping" (SessionType.tEnd, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "Shipping" "ExternalMailserver" "Success" "unit" ⟨_, hTr⟩
  · -- CS_117
    have hP_C : NetworkHasQueue CS_117 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_117, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_118
    have hP_C : NetworkHasQueue CS_118 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_118, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mHGValidCC] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans StConfTp (st_label.inp "HTTP_Gateway" "ValidCC" "unit") SessionType.tEnd :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mHGValidCC] (QueueMessage.msg "HTTP_Gateway" "ValidCC" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("ExternalClient", (StConfTp, [mHGValidCC])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_118])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit") ((path.seq i).replace "ExternalClient" (SessionType.tEnd, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "ExternalClient" "HTTP_Gateway" "ValidCC" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_119
    have hP_C : NetworkHasQueue CS_119 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_119, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mEMSuccess] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans ShipB (st_label.inp "ExternalMailserver" "Success" "unit") SessionType.tEnd :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mEMSuccess] (QueueMessage.msg "ExternalMailserver" "Success" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("Shipping", (ShipB, [mEMSuccess])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_119])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "Shipping" "ExternalMailserver" "Success" "unit") ((path.seq i).replace "Shipping" (SessionType.tEnd, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "Shipping" "ExternalMailserver" "Success" "unit" ⟨_, hTr⟩
  · -- CS_120
    have hP_C : NetworkHasQueue CS_120 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_120, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      have hmem : QueueMessage.msg q lab S ∈ [mPayMakeCharge] :=
        Queue.dequeue_mem hQ
      simp only [List.mem_singleton] at hmem
      cases hmem
      have hST : st_trans Bank (st_label.inp "Payment" "MakeCharge" "unit") SessionType.tEnd :=
        st_transb_sound (n := 1) (by decide)
      have hQdeq : Queue.dequeue [mPayMakeCharge] (QueueMessage.msg "Payment" "MakeCharge" "unit") = some ([] : Queue) := by decide
      have hmemSeq : ("ExternalBank", (Bank, [mPayMakeCharge])) ∈ path.seq i :=
        (Network.mem_reordered hperm).mpr (by simp [CS_120])
      have hTr : net_trans (path.seq i) (net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit") ((path.seq i).replace "ExternalBank" (SessionType.tEnd, [])) :=
        net_trans.dequeue (sq_trans.dequeue hST hQdeq) hmemSeq
      exact (hfair i).2 "ExternalBank" "Payment" "MakeCharge" "unit" ⟨_, hTr⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_121
    have hP_C : NetworkHasQueue CS_121 p Qp :=
      (Network.hasQueue_reordered hperm).mp hmemP
    obtain ⟨T, hPC⟩ := hP_C
    simp only [CS_121, List.mem_cons, List.mem_nil_iff, or_false] at hPC
    rcases hPC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · obtain ⟨_, hQ⟩ := hdeq
      simp [Queue.dequeue, Queue.dequeue.go] at hQ

theorem Net_outputLive : IsOutputLiveNetwork Net :=
  ⟨storeOL_inf, Net_noOrphanStuck⟩

end Store

import Nest.Examples.Store

namespace Store


theorem storeHHD : ∀ C ∈ Cs, ∀ (p q : Role) (Qp Qq : Queue),
    NetworkHasQueue C p Qp → NetworkHasQueue C q Qq →
    QueueContainsFrom Qp q → ¬ QueueContainsFrom Qq p := by
  intro C hC
  simp only [Cs, List.mem_cons, List.mem_nil_iff, or_false] at hC
  rcases hC with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- CS_0
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_0, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_1
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_1, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_2
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_2, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_3
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_3, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_4
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_4, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_5
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_5, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_6
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_6, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_7
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_7, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_8
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_8, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_9
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_9, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_10
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_10, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_11
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_11, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_12
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_12, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_13
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_13, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_14
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_14, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_15
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_15, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_16
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_16, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_17
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_17, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_18
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_18, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_19
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_19, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_20
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_20, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_21
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_21, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_22
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_22, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_23
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_23, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_24
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_24, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_25
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_25, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_26
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_26, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_27
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_27, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_28
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_28, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_29
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_29, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_30
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_30, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_31
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_31, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_32
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_32, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_33
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_33, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
  · -- CS_34
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_34, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_35
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_35, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_36
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_36, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_37
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_37, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_38
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_38, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_39
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_39, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
  · -- CS_40
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_40, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_41
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_41, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_42
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_42, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_43
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_43, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
  · -- CS_44
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_44, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_45
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_45, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_46
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_46, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_47
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_47, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
  · -- CS_48
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_48, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_49
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_49, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_50
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_50, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_51
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_51, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
  · -- CS_52
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_52, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_53
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_53, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_54
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_54, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_55
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_55, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
  · -- CS_56
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_56, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
  · -- CS_57
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_57, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_58
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_58, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_59
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_59, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_60
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_60, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
  · -- CS_61
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_61, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_62
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_62, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_63
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_63, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_64
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_64, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
  · -- CS_65
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_65, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_66
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_66, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_67
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_67, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_68
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_68, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_69
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_69, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
  · -- CS_70
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_70, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_71
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_71, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_72
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_72, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_73
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_73, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
  · -- CS_74
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_74, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_75
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_75, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_76
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_76, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_77
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_77, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
  · -- CS_78
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_78, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_79
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_79, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_80
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_80, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_81
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_81, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_82
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_82, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
  · -- CS_83
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_83, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_84
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_84, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_85
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_85, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_86
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_86, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
  · -- CS_87
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_87, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_88
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_88, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_89
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_89, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_90
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_90, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
  · -- CS_91
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_91, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_92
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_92, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_93
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_93, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_94
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_94, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_95
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_95, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
  · -- CS_96
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_96, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_97
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_97, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_98
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_98, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_99
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_99, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
  · -- CS_100
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_100, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_101
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_101, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_102
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_102, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
  · -- CS_103
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_103, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
  · -- CS_104
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_104, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_105
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_105, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_106
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_106, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_107
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_107, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
  · -- CS_108
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_108, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_109
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_109, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_110
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_110, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
  · -- CS_111
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_111, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_112
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_112, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_113
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_113, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
  · -- CS_114
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_114, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_115
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_115, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_116
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_116, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
  · -- CS_117
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_117, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_118
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_118, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_119
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_119, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
  · -- CS_120
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_120, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro _ hCq
      obtain ⟨lab, S, hmem⟩ := hCq
      have hmem' := hmem.to_mem
      simp at hmem'
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro _ hCq; exact noContainsNil hCq
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
  · -- CS_121
    intro p q Qp Qq hP hQ
    obtain ⟨T, hP⟩ := hP
    obtain ⟨U, hQ⟩ := hQ
    simp only [CS_121, List.mem_cons, List.mem_nil_iff, or_false] at hP hQ
    rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hQ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil
    · intro hPq _; exact absurd hPq noContainsNil

theorem storeHNO : ∀ C ∈ Cs, IsStuckNetwork C → NoOrphanMessages C := by
  intro C hC
  simp only [Cs, List.mem_cons, List.mem_nil_iff, or_false] at hC
  rcases hC with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- CS_0 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "ExternalClient" "HTTP_Gateway" "PlaceOrder" "unit", ((CS_0.replace "ExternalClient" (StCB0, [])).replace "HTTP_Gateway" (HTTP, [QueueMessage.msg "ExternalClient" "PlaceOrder" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_0 (net_label.τ_comm "ExternalClient" "HTTP_Gateway" "PlaceOrder" "unit") ((CS_0.replace "ExternalClient" (StCB0, [])).replace "HTTP_Gateway" (HTTP, [QueueMessage.msg "ExternalClient" "PlaceOrder" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_1 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "HTTP_Gateway" "ExternalClient" "PlaceOrder" "unit", (CS_1.replace "HTTP_Gateway" (H1, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_1).Nodup) (show net_transb 1 CS_1 (net_label.τ_dequeue "HTTP_Gateway" "ExternalClient" "PlaceOrder" "unit") (CS_1.replace "HTTP_Gateway" (H1, [])) = true from by decide)⟩) hStuck
  · -- CS_2 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "HTTP_Gateway" "Inventory" "GetSKUDetails" "unit", ((CS_2.replace "HTTP_Gateway" (H2, [])).replace "Inventory" (Inventory, [QueueMessage.msg "HTTP_Gateway" "GetSKUDetails" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_2 (net_label.τ_comm "HTTP_Gateway" "Inventory" "GetSKUDetails" "unit") ((CS_2.replace "HTTP_Gateway" (H2, [])).replace "Inventory" (Inventory, [QueueMessage.msg "HTTP_Gateway" "GetSKUDetails" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_3 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Inventory" "HTTP_Gateway" "GetSKUDetails" "unit", (CS_3.replace "Inventory" (InvA, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_3).Nodup) (show net_transb 1 CS_3 (net_label.τ_dequeue "Inventory" "HTTP_Gateway" "GetSKUDetails" "unit") (CS_3.replace "Inventory" (InvA, [])) = true from by decide)⟩) hStuck
  · -- CS_4 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Inventory" "HTTP_Gateway" "SKUDetails" "unit", ((CS_4.replace "Inventory" (InvB, [])).replace "HTTP_Gateway" (H2, [QueueMessage.msg "Inventory" "SKUDetails" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_4 (net_label.τ_comm "Inventory" "HTTP_Gateway" "SKUDetails" "unit") ((CS_4.replace "Inventory" (InvB, [])).replace "HTTP_Gateway" (H2, [QueueMessage.msg "Inventory" "SKUDetails" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_5 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "HTTP_Gateway" "Inventory" "SKUDetails" "unit", (CS_5.replace "HTTP_Gateway" (H3, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_5).Nodup) (show net_transb 1 CS_5 (net_label.τ_dequeue "HTTP_Gateway" "Inventory" "SKUDetails" "unit") (CS_5.replace "HTTP_Gateway" (H3, [])) = true from by decide)⟩) hStuck
  · -- CS_6 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "HTTP_Gateway" "ExternalClient" "SKUDetails" "unit", ((CS_6.replace "HTTP_Gateway" (HRec, [])).replace "ExternalClient" (StCB0, [QueueMessage.msg "HTTP_Gateway" "SKUDetails" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_6 (net_label.τ_comm "HTTP_Gateway" "ExternalClient" "SKUDetails" "unit") ((CS_6.replace "HTTP_Gateway" (HRec, [])).replace "ExternalClient" (StCB0, [QueueMessage.msg "HTTP_Gateway" "SKUDetails" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_7 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "SKUDetails" "unit", (CS_7.replace "ExternalClient" (StRec, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_7).Nodup) (show net_transb 1 CS_7 (net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "SKUDetails" "unit") (CS_7.replace "ExternalClient" (StRec, [])) = true from by decide)⟩) hStuck
  · -- CS_8 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "ExternalClient" "HTTP_Gateway" "ConfirmOrder" "unit", ((CS_8.replace "ExternalClient" (StConfTp, [])).replace "HTTP_Gateway" (HRec, [QueueMessage.msg "ExternalClient" "ConfirmOrder" "unit"])), by trivial, net_transb_comm_sound (show net_transb 2 CS_8 (net_label.τ_comm "ExternalClient" "HTTP_Gateway" "ConfirmOrder" "unit") ((CS_8.replace "ExternalClient" (StConfTp, [])).replace "HTTP_Gateway" (HRec, [QueueMessage.msg "ExternalClient" "ConfirmOrder" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_9 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "HTTP_Gateway" "ExternalClient" "ConfirmOrder" "unit", (CS_9.replace "HTTP_Gateway" (H4p, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_9).Nodup) (show net_transb 2 CS_9 (net_label.τ_dequeue "HTTP_Gateway" "ExternalClient" "ConfirmOrder" "unit") (CS_9.replace "HTTP_Gateway" (H4p, [])) = true from by decide)⟩) hStuck
  · -- CS_10 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "HTTP_Gateway" "ExternalClient" "CancelOrder" "unit", (CS_10.replace "HTTP_Gateway" (H5, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_10).Nodup) (show net_transb 2 CS_10 (net_label.τ_dequeue "HTTP_Gateway" "ExternalClient" "CancelOrder" "unit") (CS_10.replace "HTTP_Gateway" (H5, [])) = true from by decide)⟩) hStuck
  · -- CS_11 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "HTTP_Gateway" "Payment" "VerifyCC" "unit", ((CS_11.replace "HTTP_Gateway" (H6p, [])).replace "Payment" (Payment, [QueueMessage.msg "HTTP_Gateway" "VerifyCC" "unit"])), by trivial, net_transb_comm_sound (show net_transb 2 CS_11 (net_label.τ_comm "HTTP_Gateway" "Payment" "VerifyCC" "unit") ((CS_11.replace "HTTP_Gateway" (H6p, [])).replace "Payment" (Payment, [QueueMessage.msg "HTTP_Gateway" "VerifyCC" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_12 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "HTTP_Gateway" "ExternalClient" "Cancel" "unit", ((CS_12.replace "HTTP_Gateway" (SessionType.tEnd, [])).replace "ExternalClient" (StCancTp, [QueueMessage.msg "HTTP_Gateway" "Cancel" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_12 (net_label.τ_comm "HTTP_Gateway" "ExternalClient" "Cancel" "unit") ((CS_12.replace "HTTP_Gateway" (SessionType.tEnd, [])).replace "ExternalClient" (StCancTp, [QueueMessage.msg "HTTP_Gateway" "Cancel" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_13 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Payment" "HTTP_Gateway" "VerifyCC" "unit", (CS_13.replace "Payment" (PayISub, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_13).Nodup) (show net_transb 2 CS_13 (net_label.τ_dequeue "Payment" "HTTP_Gateway" "VerifyCC" "unit") (CS_13.replace "Payment" (PayISub, [])) = true from by decide)⟩) hStuck
  · -- CS_14 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "Cancel" "unit", (CS_14.replace "ExternalClient" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_14).Nodup) (show net_transb 1 CS_14 (net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "Cancel" "unit") (CS_14.replace "ExternalClient" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_15 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Payment" "HTTP_Gateway" "ValidCC" "unit", ((CS_15.replace "Payment" (PayTa, [])).replace "HTTP_Gateway" (H6p, [QueueMessage.msg "Payment" "ValidCC" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_15 (net_label.τ_comm "Payment" "HTTP_Gateway" "ValidCC" "unit") ((CS_15.replace "Payment" (PayTa, [])).replace "HTTP_Gateway" (H6p, [QueueMessage.msg "Payment" "ValidCC" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_16 (stuck, all queues empty)
    intro _ r T Q p lab S Q' hmem hQ
    simp only [CS_16, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · simp [Queue.dequeue, Queue.dequeue.go] at hQ
  · -- CS_17 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "HTTP_Gateway" "Payment" "ValidCC" "unit", (CS_17.replace "HTTP_Gateway" (H7, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_17).Nodup) (show net_transb 1 CS_17 (net_label.τ_dequeue "HTTP_Gateway" "Payment" "ValidCC" "unit") (CS_17.replace "HTTP_Gateway" (H7, [])) = true from by decide)⟩) hStuck
  · -- CS_18 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "HTTP_Gateway" "Payment" "InvalidCC" "unit", (CS_18.replace "HTTP_Gateway" (H8p, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_18).Nodup) (show net_transb 1 CS_18 (net_label.τ_dequeue "HTTP_Gateway" "Payment" "InvalidCC" "unit") (CS_18.replace "HTTP_Gateway" (H8p, [])) = true from by decide)⟩) hStuck
  · -- CS_19 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "HTTP_Gateway" "Payment" "MakeCharge" "unit", ((CS_19.replace "HTTP_Gateway" (H9, [])).replace "Payment" (PayTa, [QueueMessage.msg "HTTP_Gateway" "MakeCharge" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_19 (net_label.τ_comm "HTTP_Gateway" "Payment" "MakeCharge" "unit") ((CS_19.replace "HTTP_Gateway" (H9, [])).replace "Payment" (PayTa, [QueueMessage.msg "HTTP_Gateway" "MakeCharge" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_20 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "HTTP_Gateway" "ExternalClient" "InvalidCC" "unit", ((CS_20.replace "HTTP_Gateway" (HRec, [])).replace "ExternalClient" (StConfTp, [QueueMessage.msg "HTTP_Gateway" "InvalidCC" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_20 (net_label.τ_comm "HTTP_Gateway" "ExternalClient" "InvalidCC" "unit") ((CS_20.replace "HTTP_Gateway" (HRec, [])).replace "ExternalClient" (StConfTp, [QueueMessage.msg "HTTP_Gateway" "InvalidCC" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_21 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "HTTP_Gateway" "Inventory" "MakeOrder" "unit", ((CS_21.replace "HTTP_Gateway" (H10, [])).replace "Inventory" (InvB, [QueueMessage.msg "HTTP_Gateway" "MakeOrder" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_21 (net_label.τ_comm "HTTP_Gateway" "Inventory" "MakeOrder" "unit") ((CS_21.replace "HTTP_Gateway" (H10, [])).replace "Inventory" (InvB, [QueueMessage.msg "HTTP_Gateway" "MakeOrder" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_22 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "InvalidCC" "unit", (CS_22.replace "ExternalClient" (StRec, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_22).Nodup) (show net_transb 1 CS_22 (net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "InvalidCC" "unit") (CS_22.replace "ExternalClient" (StRec, [])) = true from by decide)⟩) hStuck
  · -- CS_23 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "HTTP_Gateway" "Inventory" "MakeOrder" "unit", ((CS_23.replace "HTTP_Gateway" (H10, [])).replace "Inventory" (InvB, [QueueMessage.msg "HTTP_Gateway" "MakeOrder" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_23 (net_label.τ_comm "HTTP_Gateway" "Inventory" "MakeOrder" "unit") ((CS_23.replace "HTTP_Gateway" (H10, [])).replace "Inventory" (InvB, [QueueMessage.msg "HTTP_Gateway" "MakeOrder" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_24 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "HTTP_Gateway" "ExternalClient" "ValidCC" "unit", ((CS_24.replace "HTTP_Gateway" (SessionType.tEnd, [])).replace "ExternalClient" (StConfTp, [QueueMessage.msg "HTTP_Gateway" "ValidCC" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_24 (net_label.τ_comm "HTTP_Gateway" "ExternalClient" "ValidCC" "unit") ((CS_24.replace "HTTP_Gateway" (SessionType.tEnd, [])).replace "ExternalClient" (StConfTp, [QueueMessage.msg "HTTP_Gateway" "ValidCC" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_25 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit", (CS_25.replace "ExternalBank" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_25).Nodup) (show net_transb 1 CS_25 (net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit") (CS_25.replace "ExternalBank" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_26 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "HTTP_Gateway" "ExternalClient" "ValidCC" "unit", ((CS_26.replace "HTTP_Gateway" (SessionType.tEnd, [])).replace "ExternalClient" (StConfTp, [QueueMessage.msg "HTTP_Gateway" "ValidCC" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_26 (net_label.τ_comm "HTTP_Gateway" "ExternalClient" "ValidCC" "unit") ((CS_26.replace "HTTP_Gateway" (SessionType.tEnd, [])).replace "ExternalClient" (StConfTp, [QueueMessage.msg "HTTP_Gateway" "ValidCC" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_27 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "HTTP_Gateway" "ExternalClient" "ValidCC" "unit", ((CS_27.replace "HTTP_Gateway" (SessionType.tEnd, [])).replace "ExternalClient" (StConfTp, [QueueMessage.msg "HTTP_Gateway" "ValidCC" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_27 (net_label.τ_comm "HTTP_Gateway" "ExternalClient" "ValidCC" "unit") ((CS_27.replace "HTTP_Gateway" (SessionType.tEnd, [])).replace "ExternalClient" (StConfTp, [QueueMessage.msg "HTTP_Gateway" "ValidCC" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_28 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit", (CS_28.replace "ExternalClient" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_28).Nodup) (show net_transb 1 CS_28 (net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit") (CS_28.replace "ExternalClient" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_29 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "HTTP_Gateway" "Inventory" "MakeOrder" "unit", ((CS_29.replace "HTTP_Gateway" (H10, [])).replace "Inventory" (InvB, [QueueMessage.msg "HTTP_Gateway" "MakeOrder" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_29 (net_label.τ_comm "HTTP_Gateway" "Inventory" "MakeOrder" "unit") ((CS_29.replace "HTTP_Gateway" (H10, [])).replace "Inventory" (InvB, [QueueMessage.msg "HTTP_Gateway" "MakeOrder" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_30 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit", (CS_30.replace "ExternalBank" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_30).Nodup) (show net_transb 1 CS_30 (net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit") (CS_30.replace "ExternalBank" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_31 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "HTTP_Gateway" "ExternalClient" "ValidCC" "unit", ((CS_31.replace "HTTP_Gateway" (SessionType.tEnd, [])).replace "ExternalClient" (StConfTp, [QueueMessage.msg "HTTP_Gateway" "ValidCC" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_31 (net_label.τ_comm "HTTP_Gateway" "ExternalClient" "ValidCC" "unit") ((CS_31.replace "HTTP_Gateway" (SessionType.tEnd, [])).replace "ExternalClient" (StConfTp, [QueueMessage.msg "HTTP_Gateway" "ValidCC" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_32 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit", (CS_32.replace "ExternalClient" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_32).Nodup) (show net_transb 1 CS_32 (net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit") (CS_32.replace "ExternalClient" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_33 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "HTTP_Gateway" "ExternalClient" "ValidCC" "unit", ((CS_33.replace "HTTP_Gateway" (SessionType.tEnd, [])).replace "ExternalClient" (StConfTp, [QueueMessage.msg "HTTP_Gateway" "ValidCC" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_33 (net_label.τ_comm "HTTP_Gateway" "ExternalClient" "ValidCC" "unit") ((CS_33.replace "HTTP_Gateway" (SessionType.tEnd, [])).replace "ExternalClient" (StConfTp, [QueueMessage.msg "HTTP_Gateway" "ValidCC" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_34 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit", (CS_34.replace "ExternalClient" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_34).Nodup) (show net_transb 1 CS_34 (net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit") (CS_34.replace "ExternalClient" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_35 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Inventory" "HTTP_Gateway" "MakeOrder" "unit", (CS_35.replace "Inventory" (InvC, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_35).Nodup) (show net_transb 1 CS_35 (net_label.τ_dequeue "Inventory" "HTTP_Gateway" "MakeOrder" "unit") (CS_35.replace "Inventory" (InvC, [])) = true from by decide)⟩) hStuck
  · -- CS_36 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "HTTP_Gateway" "ExternalClient" "ValidCC" "unit", ((CS_36.replace "HTTP_Gateway" (SessionType.tEnd, [])).replace "ExternalClient" (StConfTp, [QueueMessage.msg "HTTP_Gateway" "ValidCC" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_36 (net_label.τ_comm "HTTP_Gateway" "ExternalClient" "ValidCC" "unit") ((CS_36.replace "HTTP_Gateway" (SessionType.tEnd, [])).replace "ExternalClient" (StConfTp, [QueueMessage.msg "HTTP_Gateway" "ValidCC" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_37 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit", (CS_37.replace "ExternalBank" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_37).Nodup) (show net_transb 1 CS_37 (net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit") (CS_37.replace "ExternalBank" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_38 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit", (CS_38.replace "ExternalBank" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_38).Nodup) (show net_transb 1 CS_38 (net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit") (CS_38.replace "ExternalBank" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_39 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "HTTP_Gateway" "ExternalClient" "ValidCC" "unit", ((CS_39.replace "HTTP_Gateway" (SessionType.tEnd, [])).replace "ExternalClient" (StConfTp, [QueueMessage.msg "HTTP_Gateway" "ValidCC" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_39 (net_label.τ_comm "HTTP_Gateway" "ExternalClient" "ValidCC" "unit") ((CS_39.replace "HTTP_Gateway" (SessionType.tEnd, [])).replace "ExternalClient" (StConfTp, [QueueMessage.msg "HTTP_Gateway" "ValidCC" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_40 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit", (CS_40.replace "ExternalClient" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_40).Nodup) (show net_transb 1 CS_40 (net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit") (CS_40.replace "ExternalClient" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_41 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Inventory" "HTTP_Gateway" "MakeOrder" "unit", (CS_41.replace "Inventory" (InvC, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_41).Nodup) (show net_transb 1 CS_41 (net_label.τ_dequeue "Inventory" "HTTP_Gateway" "MakeOrder" "unit") (CS_41.replace "Inventory" (InvC, [])) = true from by decide)⟩) hStuck
  · -- CS_42 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "HTTP_Gateway" "ExternalClient" "ValidCC" "unit", ((CS_42.replace "HTTP_Gateway" (SessionType.tEnd, [])).replace "ExternalClient" (StConfTp, [QueueMessage.msg "HTTP_Gateway" "ValidCC" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_42 (net_label.τ_comm "HTTP_Gateway" "ExternalClient" "ValidCC" "unit") ((CS_42.replace "HTTP_Gateway" (SessionType.tEnd, [])).replace "ExternalClient" (StConfTp, [QueueMessage.msg "HTTP_Gateway" "ValidCC" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_43 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit", (CS_43.replace "ExternalClient" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_43).Nodup) (show net_transb 1 CS_43 (net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit") (CS_43.replace "ExternalClient" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_44 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Inventory" "Shipping" "ShipOrder" "unit", ((CS_44.replace "Inventory" (SessionType.tEnd, [])).replace "Shipping" (Shipping, [QueueMessage.msg "Inventory" "ShipOrder" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_44 (net_label.τ_comm "Inventory" "Shipping" "ShipOrder" "unit") ((CS_44.replace "Inventory" (SessionType.tEnd, [])).replace "Shipping" (Shipping, [QueueMessage.msg "Inventory" "ShipOrder" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_45 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "HTTP_Gateway" "ExternalClient" "ValidCC" "unit", ((CS_45.replace "HTTP_Gateway" (SessionType.tEnd, [])).replace "ExternalClient" (StConfTp, [QueueMessage.msg "HTTP_Gateway" "ValidCC" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_45 (net_label.τ_comm "HTTP_Gateway" "ExternalClient" "ValidCC" "unit") ((CS_45.replace "HTTP_Gateway" (SessionType.tEnd, [])).replace "ExternalClient" (StConfTp, [QueueMessage.msg "HTTP_Gateway" "ValidCC" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_46 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit", (CS_46.replace "ExternalClient" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_46).Nodup) (show net_transb 1 CS_46 (net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit") (CS_46.replace "ExternalClient" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_47 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit", (CS_47.replace "ExternalBank" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_47).Nodup) (show net_transb 1 CS_47 (net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit") (CS_47.replace "ExternalBank" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_48 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit", (CS_48.replace "ExternalBank" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_48).Nodup) (show net_transb 1 CS_48 (net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit") (CS_48.replace "ExternalBank" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_49 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit", (CS_49.replace "ExternalBank" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_49).Nodup) (show net_transb 1 CS_49 (net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit") (CS_49.replace "ExternalBank" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_50 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "HTTP_Gateway" "ExternalClient" "ValidCC" "unit", ((CS_50.replace "HTTP_Gateway" (SessionType.tEnd, [])).replace "ExternalClient" (StConfTp, [QueueMessage.msg "HTTP_Gateway" "ValidCC" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_50 (net_label.τ_comm "HTTP_Gateway" "ExternalClient" "ValidCC" "unit") ((CS_50.replace "HTTP_Gateway" (SessionType.tEnd, [])).replace "ExternalClient" (StConfTp, [QueueMessage.msg "HTTP_Gateway" "ValidCC" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_51 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit", (CS_51.replace "ExternalClient" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_51).Nodup) (show net_transb 1 CS_51 (net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit") (CS_51.replace "ExternalClient" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_52 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Inventory" "Shipping" "ShipOrder" "unit", ((CS_52.replace "Inventory" (SessionType.tEnd, [])).replace "Shipping" (Shipping, [QueueMessage.msg "Inventory" "ShipOrder" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_52 (net_label.τ_comm "Inventory" "Shipping" "ShipOrder" "unit") ((CS_52.replace "Inventory" (SessionType.tEnd, [])).replace "Shipping" (Shipping, [QueueMessage.msg "Inventory" "ShipOrder" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_53 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "ExternalMailserver" "Shipping" "SendOrderShippedEmail" "unit", (CS_53.replace "ExternalMailserver" (EmailA, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_53).Nodup) (show net_transb 1 CS_53 (net_label.τ_dequeue "ExternalMailserver" "Shipping" "SendOrderShippedEmail" "unit") (CS_53.replace "ExternalMailserver" (EmailA, [])) = true from by decide)⟩) hStuck
  · -- CS_54 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit", (CS_54.replace "ExternalClient" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_54).Nodup) (show net_transb 1 CS_54 (net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit") (CS_54.replace "ExternalClient" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_55 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Payment" "HTTP_Gateway" "MakeCharge" "unit", (CS_55.replace "Payment" (PayIBank, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_55).Nodup) (show net_transb 1 CS_55 (net_label.τ_dequeue "Payment" "HTTP_Gateway" "MakeCharge" "unit") (CS_55.replace "Payment" (PayIBank, [])) = true from by decide)⟩) hStuck
  · -- CS_56 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "HTTP_Gateway" "ExternalClient" "ValidCC" "unit", ((CS_56.replace "HTTP_Gateway" (SessionType.tEnd, [])).replace "ExternalClient" (StConfTp, [QueueMessage.msg "HTTP_Gateway" "ValidCC" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_56 (net_label.τ_comm "HTTP_Gateway" "ExternalClient" "ValidCC" "unit") ((CS_56.replace "HTTP_Gateway" (SessionType.tEnd, [])).replace "ExternalClient" (StConfTp, [QueueMessage.msg "HTTP_Gateway" "ValidCC" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_57 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit", (CS_57.replace "ExternalClient" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_57).Nodup) (show net_transb 1 CS_57 (net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit") (CS_57.replace "ExternalClient" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_58 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Inventory" "HTTP_Gateway" "MakeOrder" "unit", (CS_58.replace "Inventory" (InvC, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_58).Nodup) (show net_transb 1 CS_58 (net_label.τ_dequeue "Inventory" "HTTP_Gateway" "MakeOrder" "unit") (CS_58.replace "Inventory" (InvC, [])) = true from by decide)⟩) hStuck
  · -- CS_59 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit", (CS_59.replace "ExternalBank" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_59).Nodup) (show net_transb 1 CS_59 (net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit") (CS_59.replace "ExternalBank" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_60 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit", (CS_60.replace "ExternalBank" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_60).Nodup) (show net_transb 1 CS_60 (net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit") (CS_60.replace "ExternalBank" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_61 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit", (CS_61.replace "ExternalBank" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_61).Nodup) (show net_transb 1 CS_61 (net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit") (CS_61.replace "ExternalBank" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_62 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "ExternalMailserver" "Shipping" "SendOrderShippedEmail" "unit", (CS_62.replace "ExternalMailserver" (EmailA, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_62).Nodup) (show net_transb 1 CS_62 (net_label.τ_dequeue "ExternalMailserver" "Shipping" "SendOrderShippedEmail" "unit") (CS_62.replace "ExternalMailserver" (EmailA, [])) = true from by decide)⟩) hStuck
  · -- CS_63 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit", (CS_63.replace "ExternalClient" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_63).Nodup) (show net_transb 1 CS_63 (net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit") (CS_63.replace "ExternalClient" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_64 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Payment" "ExternalBank" "MakeCharge" "unit", ((CS_64.replace "Payment" (SessionType.tEnd, [])).replace "ExternalBank" (Bank, [QueueMessage.msg "Payment" "MakeCharge" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_64 (net_label.τ_comm "Payment" "ExternalBank" "MakeCharge" "unit") ((CS_64.replace "Payment" (SessionType.tEnd, [])).replace "ExternalBank" (Bank, [QueueMessage.msg "Payment" "MakeCharge" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_65 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "ExternalMailserver" "Shipping" "Success" "unit", ((CS_65.replace "ExternalMailserver" (SessionType.tEnd, [])).replace "Shipping" (ShipB, [QueueMessage.msg "ExternalMailserver" "Success" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_65 (net_label.τ_comm "ExternalMailserver" "Shipping" "Success" "unit") ((CS_65.replace "ExternalMailserver" (SessionType.tEnd, [])).replace "Shipping" (ShipB, [QueueMessage.msg "ExternalMailserver" "Success" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_66 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit", (CS_66.replace "ExternalClient" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_66).Nodup) (show net_transb 1 CS_66 (net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit") (CS_66.replace "ExternalClient" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_67 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Payment" "HTTP_Gateway" "MakeCharge" "unit", (CS_67.replace "Payment" (PayIBank, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_67).Nodup) (show net_transb 1 CS_67 (net_label.τ_dequeue "Payment" "HTTP_Gateway" "MakeCharge" "unit") (CS_67.replace "Payment" (PayIBank, [])) = true from by decide)⟩) hStuck
  · -- CS_68 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "HTTP_Gateway" "ExternalClient" "ValidCC" "unit", ((CS_68.replace "HTTP_Gateway" (SessionType.tEnd, [])).replace "ExternalClient" (StConfTp, [QueueMessage.msg "HTTP_Gateway" "ValidCC" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_68 (net_label.τ_comm "HTTP_Gateway" "ExternalClient" "ValidCC" "unit") ((CS_68.replace "HTTP_Gateway" (SessionType.tEnd, [])).replace "ExternalClient" (StConfTp, [QueueMessage.msg "HTTP_Gateway" "ValidCC" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_69 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit", (CS_69.replace "ExternalClient" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_69).Nodup) (show net_transb 1 CS_69 (net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit") (CS_69.replace "ExternalClient" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_70 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Inventory" "Shipping" "ShipOrder" "unit", ((CS_70.replace "Inventory" (SessionType.tEnd, [])).replace "Shipping" (Shipping, [QueueMessage.msg "Inventory" "ShipOrder" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_70 (net_label.τ_comm "Inventory" "Shipping" "ShipOrder" "unit") ((CS_70.replace "Inventory" (SessionType.tEnd, [])).replace "Shipping" (Shipping, [QueueMessage.msg "Inventory" "ShipOrder" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_71 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit", (CS_71.replace "ExternalBank" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_71).Nodup) (show net_transb 1 CS_71 (net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit") (CS_71.replace "ExternalBank" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_72 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit", (CS_72.replace "ExternalBank" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_72).Nodup) (show net_transb 1 CS_72 (net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit") (CS_72.replace "ExternalBank" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_73 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit", (CS_73.replace "ExternalBank" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_73).Nodup) (show net_transb 1 CS_73 (net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit") (CS_73.replace "ExternalBank" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_74 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "ExternalMailserver" "Shipping" "Success" "unit", ((CS_74.replace "ExternalMailserver" (SessionType.tEnd, [])).replace "Shipping" (ShipB, [QueueMessage.msg "ExternalMailserver" "Success" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_74 (net_label.τ_comm "ExternalMailserver" "Shipping" "Success" "unit") ((CS_74.replace "ExternalMailserver" (SessionType.tEnd, [])).replace "Shipping" (ShipB, [QueueMessage.msg "ExternalMailserver" "Success" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_75 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit", (CS_75.replace "ExternalClient" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_75).Nodup) (show net_transb 1 CS_75 (net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit") (CS_75.replace "ExternalClient" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_76 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Payment" "ExternalBank" "MakeCharge" "unit", ((CS_76.replace "Payment" (SessionType.tEnd, [])).replace "ExternalBank" (Bank, [QueueMessage.msg "Payment" "MakeCharge" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_76 (net_label.τ_comm "Payment" "ExternalBank" "MakeCharge" "unit") ((CS_76.replace "Payment" (SessionType.tEnd, [])).replace "ExternalBank" (Bank, [QueueMessage.msg "Payment" "MakeCharge" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_77 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "HTTP_Gateway" "ExternalClient" "ValidCC" "unit", ((CS_77.replace "HTTP_Gateway" (SessionType.tEnd, [])).replace "ExternalClient" (StConfTp, [QueueMessage.msg "HTTP_Gateway" "ValidCC" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_77 (net_label.τ_comm "HTTP_Gateway" "ExternalClient" "ValidCC" "unit") ((CS_77.replace "HTTP_Gateway" (SessionType.tEnd, [])).replace "ExternalClient" (StConfTp, [QueueMessage.msg "HTTP_Gateway" "ValidCC" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_78 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit", (CS_78.replace "ExternalClient" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_78).Nodup) (show net_transb 1 CS_78 (net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit") (CS_78.replace "ExternalClient" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_79 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "ExternalMailserver" "Shipping" "SendOrderShippedEmail" "unit", (CS_79.replace "ExternalMailserver" (EmailA, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_79).Nodup) (show net_transb 1 CS_79 (net_label.τ_dequeue "ExternalMailserver" "Shipping" "SendOrderShippedEmail" "unit") (CS_79.replace "ExternalMailserver" (EmailA, [])) = true from by decide)⟩) hStuck
  · -- CS_80 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "ExternalMailserver" "Shipping" "SendOrderShippedEmail" "unit", (CS_80.replace "ExternalMailserver" (EmailA, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_80).Nodup) (show net_transb 1 CS_80 (net_label.τ_dequeue "ExternalMailserver" "Shipping" "SendOrderShippedEmail" "unit") (CS_80.replace "ExternalMailserver" (EmailA, [])) = true from by decide)⟩) hStuck
  · -- CS_81 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit", (CS_81.replace "ExternalClient" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_81).Nodup) (show net_transb 1 CS_81 (net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit") (CS_81.replace "ExternalClient" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_82 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Shipping" "Inventory" "ShipOrder" "unit", (CS_82.replace "Shipping" (ShipA, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_82).Nodup) (show net_transb 1 CS_82 (net_label.τ_dequeue "Shipping" "Inventory" "ShipOrder" "unit") (CS_82.replace "Shipping" (ShipA, [])) = true from by decide)⟩) hStuck
  · -- CS_83 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit", (CS_83.replace "ExternalBank" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_83).Nodup) (show net_transb 1 CS_83 (net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit") (CS_83.replace "ExternalBank" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_84 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit", (CS_84.replace "ExternalBank" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_84).Nodup) (show net_transb 1 CS_84 (net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit") (CS_84.replace "ExternalBank" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_85 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit", (CS_85.replace "ExternalBank" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_85).Nodup) (show net_transb 1 CS_85 (net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit") (CS_85.replace "ExternalBank" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_86 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "HTTP_Gateway" "ExternalClient" "ValidCC" "unit", ((CS_86.replace "HTTP_Gateway" (SessionType.tEnd, [])).replace "ExternalClient" (StConfTp, [QueueMessage.msg "HTTP_Gateway" "ValidCC" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_86 (net_label.τ_comm "HTTP_Gateway" "ExternalClient" "ValidCC" "unit") ((CS_86.replace "HTTP_Gateway" (SessionType.tEnd, [])).replace "ExternalClient" (StConfTp, [QueueMessage.msg "HTTP_Gateway" "ValidCC" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_87 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit", (CS_87.replace "ExternalClient" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_87).Nodup) (show net_transb 1 CS_87 (net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit") (CS_87.replace "ExternalClient" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_88 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "ExternalMailserver" "Shipping" "SendOrderShippedEmail" "unit", (CS_88.replace "ExternalMailserver" (EmailA, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_88).Nodup) (show net_transb 1 CS_88 (net_label.τ_dequeue "ExternalMailserver" "Shipping" "SendOrderShippedEmail" "unit") (CS_88.replace "ExternalMailserver" (EmailA, [])) = true from by decide)⟩) hStuck
  · -- CS_89 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "HTTP_Gateway" "ExternalClient" "ValidCC" "unit", ((CS_89.replace "HTTP_Gateway" (SessionType.tEnd, [])).replace "ExternalClient" (StConfTp, [QueueMessage.msg "HTTP_Gateway" "ValidCC" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_89 (net_label.τ_comm "HTTP_Gateway" "ExternalClient" "ValidCC" "unit") ((CS_89.replace "HTTP_Gateway" (SessionType.tEnd, [])).replace "ExternalClient" (StConfTp, [QueueMessage.msg "HTTP_Gateway" "ValidCC" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_90 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit", (CS_90.replace "ExternalClient" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_90).Nodup) (show net_transb 1 CS_90 (net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit") (CS_90.replace "ExternalClient" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_91 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "ExternalMailserver" "Shipping" "Success" "unit", ((CS_91.replace "ExternalMailserver" (SessionType.tEnd, [])).replace "Shipping" (ShipB, [QueueMessage.msg "ExternalMailserver" "Success" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_91 (net_label.τ_comm "ExternalMailserver" "Shipping" "Success" "unit") ((CS_91.replace "ExternalMailserver" (SessionType.tEnd, [])).replace "Shipping" (ShipB, [QueueMessage.msg "ExternalMailserver" "Success" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_92 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "ExternalMailserver" "Shipping" "Success" "unit", ((CS_92.replace "ExternalMailserver" (SessionType.tEnd, [])).replace "Shipping" (ShipB, [QueueMessage.msg "ExternalMailserver" "Success" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_92 (net_label.τ_comm "ExternalMailserver" "Shipping" "Success" "unit") ((CS_92.replace "ExternalMailserver" (SessionType.tEnd, [])).replace "Shipping" (ShipB, [QueueMessage.msg "ExternalMailserver" "Success" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_93 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit", (CS_93.replace "ExternalClient" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_93).Nodup) (show net_transb 1 CS_93 (net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit") (CS_93.replace "ExternalClient" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_94 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Shipping" "ExternalMailserver" "SendOrderShippedEmail" "unit", ((CS_94.replace "Shipping" (ShipB, [])).replace "ExternalMailserver" (Email, [QueueMessage.msg "Shipping" "SendOrderShippedEmail" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_94 (net_label.τ_comm "Shipping" "ExternalMailserver" "SendOrderShippedEmail" "unit") ((CS_94.replace "Shipping" (ShipB, [])).replace "ExternalMailserver" (Email, [QueueMessage.msg "Shipping" "SendOrderShippedEmail" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_95 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit", (CS_95.replace "ExternalBank" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_95).Nodup) (show net_transb 1 CS_95 (net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit") (CS_95.replace "ExternalBank" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_96 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit", (CS_96.replace "ExternalBank" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_96).Nodup) (show net_transb 1 CS_96 (net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit") (CS_96.replace "ExternalBank" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_97 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit", (CS_97.replace "ExternalBank" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_97).Nodup) (show net_transb 1 CS_97 (net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit") (CS_97.replace "ExternalBank" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_98 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "HTTP_Gateway" "ExternalClient" "ValidCC" "unit", ((CS_98.replace "HTTP_Gateway" (SessionType.tEnd, [])).replace "ExternalClient" (StConfTp, [QueueMessage.msg "HTTP_Gateway" "ValidCC" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_98 (net_label.τ_comm "HTTP_Gateway" "ExternalClient" "ValidCC" "unit") ((CS_98.replace "HTTP_Gateway" (SessionType.tEnd, [])).replace "ExternalClient" (StConfTp, [QueueMessage.msg "HTTP_Gateway" "ValidCC" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_99 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit", (CS_99.replace "ExternalClient" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_99).Nodup) (show net_transb 1 CS_99 (net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit") (CS_99.replace "ExternalClient" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_100 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "ExternalMailserver" "Shipping" "Success" "unit", ((CS_100.replace "ExternalMailserver" (SessionType.tEnd, [])).replace "Shipping" (ShipB, [QueueMessage.msg "ExternalMailserver" "Success" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_100 (net_label.τ_comm "ExternalMailserver" "Shipping" "Success" "unit") ((CS_100.replace "ExternalMailserver" (SessionType.tEnd, [])).replace "Shipping" (ShipB, [QueueMessage.msg "ExternalMailserver" "Success" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_101 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit", (CS_101.replace "ExternalClient" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_101).Nodup) (show net_transb 1 CS_101 (net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit") (CS_101.replace "ExternalClient" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_102 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Payment" "HTTP_Gateway" "MakeCharge" "unit", (CS_102.replace "Payment" (PayIBank, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_102).Nodup) (show net_transb 1 CS_102 (net_label.τ_dequeue "Payment" "HTTP_Gateway" "MakeCharge" "unit") (CS_102.replace "Payment" (PayIBank, [])) = true from by decide)⟩) hStuck
  · -- CS_103 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "HTTP_Gateway" "ExternalClient" "ValidCC" "unit", ((CS_103.replace "HTTP_Gateway" (SessionType.tEnd, [])).replace "ExternalClient" (StConfTp, [QueueMessage.msg "HTTP_Gateway" "ValidCC" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_103 (net_label.τ_comm "HTTP_Gateway" "ExternalClient" "ValidCC" "unit") ((CS_103.replace "HTTP_Gateway" (SessionType.tEnd, [])).replace "ExternalClient" (StConfTp, [QueueMessage.msg "HTTP_Gateway" "ValidCC" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_104 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit", (CS_104.replace "ExternalClient" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_104).Nodup) (show net_transb 1 CS_104 (net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit") (CS_104.replace "ExternalClient" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_105 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "ExternalMailserver" "Shipping" "SendOrderShippedEmail" "unit", (CS_105.replace "ExternalMailserver" (EmailA, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_105).Nodup) (show net_transb 1 CS_105 (net_label.τ_dequeue "ExternalMailserver" "Shipping" "SendOrderShippedEmail" "unit") (CS_105.replace "ExternalMailserver" (EmailA, [])) = true from by decide)⟩) hStuck
  · -- CS_106 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit", (CS_106.replace "ExternalBank" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_106).Nodup) (show net_transb 1 CS_106 (net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit") (CS_106.replace "ExternalBank" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_107 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit", (CS_107.replace "ExternalBank" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_107).Nodup) (show net_transb 1 CS_107 (net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit") (CS_107.replace "ExternalBank" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_108 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit", (CS_108.replace "ExternalBank" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_108).Nodup) (show net_transb 1 CS_108 (net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit") (CS_108.replace "ExternalBank" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_109 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit", (CS_109.replace "ExternalClient" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_109).Nodup) (show net_transb 1 CS_109 (net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit") (CS_109.replace "ExternalClient" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_110 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Payment" "ExternalBank" "MakeCharge" "unit", ((CS_110.replace "Payment" (SessionType.tEnd, [])).replace "ExternalBank" (Bank, [QueueMessage.msg "Payment" "MakeCharge" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_110 (net_label.τ_comm "Payment" "ExternalBank" "MakeCharge" "unit") ((CS_110.replace "Payment" (SessionType.tEnd, [])).replace "ExternalBank" (Bank, [QueueMessage.msg "Payment" "MakeCharge" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_111 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Payment" "HTTP_Gateway" "MakeCharge" "unit", (CS_111.replace "Payment" (PayIBank, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_111).Nodup) (show net_transb 1 CS_111 (net_label.τ_dequeue "Payment" "HTTP_Gateway" "MakeCharge" "unit") (CS_111.replace "Payment" (PayIBank, [])) = true from by decide)⟩) hStuck
  · -- CS_112 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "HTTP_Gateway" "ExternalClient" "ValidCC" "unit", ((CS_112.replace "HTTP_Gateway" (SessionType.tEnd, [])).replace "ExternalClient" (StConfTp, [QueueMessage.msg "HTTP_Gateway" "ValidCC" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_112 (net_label.τ_comm "HTTP_Gateway" "ExternalClient" "ValidCC" "unit") ((CS_112.replace "HTTP_Gateway" (SessionType.tEnd, [])).replace "ExternalClient" (StConfTp, [QueueMessage.msg "HTTP_Gateway" "ValidCC" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_113 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit", (CS_113.replace "ExternalClient" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_113).Nodup) (show net_transb 1 CS_113 (net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit") (CS_113.replace "ExternalClient" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_114 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "ExternalMailserver" "Shipping" "Success" "unit", ((CS_114.replace "ExternalMailserver" (SessionType.tEnd, [])).replace "Shipping" (ShipB, [QueueMessage.msg "ExternalMailserver" "Success" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_114 (net_label.τ_comm "ExternalMailserver" "Shipping" "Success" "unit") ((CS_114.replace "ExternalMailserver" (SessionType.tEnd, [])).replace "Shipping" (ShipB, [QueueMessage.msg "ExternalMailserver" "Success" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_115 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit", (CS_115.replace "ExternalBank" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_115).Nodup) (show net_transb 1 CS_115 (net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit") (CS_115.replace "ExternalBank" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_116 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit", (CS_116.replace "ExternalBank" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_116).Nodup) (show net_transb 1 CS_116 (net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit") (CS_116.replace "ExternalBank" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_117 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_comm "Payment" "ExternalBank" "MakeCharge" "unit", ((CS_117.replace "Payment" (SessionType.tEnd, [])).replace "ExternalBank" (Bank, [QueueMessage.msg "Payment" "MakeCharge" "unit"])), by trivial, net_transb_comm_sound (show net_transb 1 CS_117 (net_label.τ_comm "Payment" "ExternalBank" "MakeCharge" "unit") ((CS_117.replace "Payment" (SessionType.tEnd, [])).replace "ExternalBank" (Bank, [QueueMessage.msg "Payment" "MakeCharge" "unit"])) = true from by decide)⟩) hStuck
  · -- CS_118 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit", (CS_118.replace "ExternalClient" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_118).Nodup) (show net_transb 1 CS_118 (net_label.τ_dequeue "ExternalClient" "HTTP_Gateway" "ValidCC" "unit") (CS_118.replace "ExternalClient" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_119 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "Shipping" "ExternalMailserver" "Success" "unit", (CS_119.replace "Shipping" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_119).Nodup) (show net_transb 1 CS_119 (net_label.τ_dequeue "Shipping" "ExternalMailserver" "Success" "unit") (CS_119.replace "Shipping" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_120 (live: enabled-step witness)
    intro hStuck
    exact absurd (⟨net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit", (CS_120.replace "ExternalBank" (SessionType.tEnd, [])), by trivial, net_transb_single_sound (by decide : (List.map Prod.fst CS_120).Nodup) (show net_transb 1 CS_120 (net_label.τ_dequeue "ExternalBank" "Payment" "MakeCharge" "unit") (CS_120.replace "ExternalBank" (SessionType.tEnd, [])) = true from by decide)⟩) hStuck
  · -- CS_121 (stuck, all queues empty)
    intro _ r T Q p lab S Q' hmem hQ
    simp only [CS_121, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · simp [Queue.dequeue, Queue.dequeue.go] at hQ

theorem Net_halfDuplex : IsHalfDuplex Net :=
  IsHalfDuplex_of_canon_cover storeCover storeHHD

theorem Net_noOrphanStuck (N' : Network) (hStar : net_trans_star Net N')
    (hStuck : IsStuckNetwork N') : NoOrphanMessages N' :=
  noOrphan_of_canon_cover_stuck storeCover storeHNO N' hStar hStuck

end Store

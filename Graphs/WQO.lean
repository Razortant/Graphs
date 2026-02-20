import Mathlib
import Graphs.Ramsey

open Classical

variable {α : Type*} [PartialOrder α]

theorem QO_tricolor {X : Type*} [Preorder X] {f : ℕ → X} : ∃ g : ℕ ↪o ℕ, (Monotone (f ∘ g) ∨ StrictAnti (f ∘ g) ∨ (∀ i : ℕ, ∀ j : ℕ, i < j → ¬ ((f (g i) ≤ f (g j)) ∨ (f (g i) > f (g j))))) := by
  let K := SimpleGraph.completeGraph ℕ
  let C := Fin 3
  let c : K.EdgeLabeling C := by
    refine SimpleGraph.EdgeLabeling.mk ?_ ?_
    · rintro i j -
      by_cases f (min i j) ≤ f (max i j) ; exact 0
      by_cases f (min i j) > f (max i j) ; exact 1
      exact 2
    · intro i j h1
      -- have hmin : min i j = min j i := by
      --   apply le_antisymm
      --   apply le_min
      --   apply min_le_right
      --   apply min_le_left
      --   apply le_min
      --   apply min_le_right
      --   apply min_le_left
      -- have hmax : max i j = max j i := by
      --   apply le_antisymm
      --   apply max_le
      --   apply le_max_right
      --   apply le_max_left
      --   apply max_le
      --   apply le_max_right
      --   apply le_max_left
      repeat rw [← min_comm i j]
      repeat rw [← max_comm i j]

  obtain ⟨S, h1, ⟨i, h2⟩⟩ := SimpleGraph.ramsey2 c
  simp [c, SimpleGraph.EdgeLabeling.get_mk] at h2
  have : Infinite S := Set.infinite_coe_iff.mpr h1
  let g := Nat.orderEmbeddingOfSet S
  use g
  have h5 {i : ℕ} : g i ∈ S := by simp [g]
  fin_cases i
  · simp at h2
    left
    rw [monotone_iff_forall_lt]
    intro a b h3
    simp
    have h4 : g a < g b := by
      rw [OrderEmbedding.lt_iff_lt]
      exact h3
    specialize h2 (g a) h5 (g b) h5
    have h6 : min (g a) (g b) = g a := by
      rw [min_eq_left_iff]
      apply LT.lt.le
      exact h4
    have h7 : max (g a) (g b) = g b := by
      rw [max_eq_right_iff]
      apply LT.lt.le
      exact h4
    rw [← h6]
    nth_rw 2 [← h7]
    have h8 : K.Adj (g a) (g b) := by
      simp [K]
      intro h
      apply h3.ne
      exact h
    specialize h2 h8
    by_contra this2
    apply h2 at this2
    by_cases P : f (max (g a) (g b)) < f (min (g a) (g b))
    simp [P] at this2
    simp [P] at this2
    exact (by decide : (2 : Fin 3) ≠ 0) this2
  · right
    left
    unfold StrictAnti
    intro a b h3
    simp
    have h4 : g a < g b := by
      rw [OrderEmbedding.lt_iff_lt]
      exact h3
    specialize h2 (g a) h5 (g b) h5
    have h6 : min (g a) (g b) = g a := by
      rw [min_eq_left_iff]
      apply LT.lt.le
      exact h4
    have h7 : max (g a) (g b) = g b := by
      rw [max_eq_right_iff]
      apply LT.lt.le
      exact h4
    rw [← h6]
    nth_rw 1 [← h7]
    have h8 : K.Adj (g a) (g b) := by
      simp [K]
      intro h
      apply h3.ne
      exact h
    specialize h2 h8
    by_cases P : f (min (g a) (g b)) ≤ f (max (g a) (g b))
    simp [P] at h2
    simp [P] at h2
    by_contra this2
    apply h2 at this2
    exact (by decide : (2 : Fin 3) ≠ 1) this2
  · right
    right
    intro a b hab P
    specialize h2 (g a) h5 (g b) h5
    simp at h2
    by_cases h3 : a < b
    have h8 : K.Adj (g a) (g b) := by
      simp [K]
      intro h
      apply h3.ne
      exact h
    specialize h2 h8
    have h4 : g a < g b := by
      rw [OrderEmbedding.lt_iff_lt]
      exact h3
    have h6 : min (g a) (g b) = g a := by
      rw [min_eq_left_iff]
      apply LT.lt.le
      exact h4
    have h7 : max (g a) (g b) = g b := by
      rw [max_eq_right_iff]
      apply LT.lt.le
      exact h4
    simp [h6, h7] at h2
    cases' P with P1 P2
    · simp [P1] at h2
      exact (by decide : 0 ≠ (2 : Fin 3)) h2
    simp [P2,not_le_of_gt P2] at h2
    exact (by decide : 1 ≠ (2 : Fin 3)) h2
    contradiction


theorem StrictAnti_iff_descending {X : Type*} [Preorder X] {f : ℕ → X} :
    StrictAnti f ↔ ∀ n, f (n + 1) < f n := by
  refine ⟨?_, strictAnti_nat_of_succ_lt⟩
  intro h n
  exact h $ lt_add_one n

theorem WQO_iff : WellQuasiOrderedLE α ↔
    (∀ s : Set α, IsAntichain (· ≤ ·) s → Set.Finite s) ∧
    (∀ f : ℕ → α, ¬ StrictAnti f) := by
  rw [wellQuasiOrderedLE_iff, and_comm]
  simp [WellFoundedLT, isWellFounded_iff, wellFounded_iff_isEmpty_descending_chain,
    ← StrictAnti_iff_descending, isEmpty_subtype]

def FinsetLE (s t : Finset α) : Prop := ∃ f : s ↪ t, ∀ x, x.val ≤ f x

-- Lemma 12.1.3
theorem Higman (h : WellQuasiOrderedLE α) : WellQuasiOrdered (FinsetLE (α := α)) := by
  by_contra h1
  unfold WellQuasiOrdered at h1
  simp at h1
  obtain ⟨A,hA⟩ := h1
  unfold FinsetLE at hA
  simp at hA
  let BB (A : ℕ → Finset α) (n : ℕ) := {B : ℕ → Finset α | (∀ i j : ℕ, i<j → ¬ B i ≤ B j) ∧ (∀ i < n, A i = B i)}
  let BBcard (A : ℕ → Finset α) (n : ℕ) := {i : ℕ | ∃ B : ℕ → Finset α, B ∈ BB A n ∧ (B n).card = i}
  let BBmin (A : ℕ → Finset α) (n : ℕ) := {B ∈ BB A n | ∀ B1 ∈ BB A n, (B n).card ≤ (B1 n).card}
  have hBBmin (A : ℕ → Finset α) (n : ℕ) : Nonempty (BB A n) → Nonempty (BBmin A n) := by
    intro hBB
    obtain ⟨B, hB⟩ := hBB
    have hcard : (B n).card ∈ BBcard A n := by
      rw [Set.mem_setOf]
      use B
    let Bcard := (B n).card
    rw [Set.nonempty_coe_sort,Set.nonempty_def]
    have hBBcard : ∃ i, i ∈ BBcard A n := by use (B n).card
    let m := Nat.find hBBcard
    have hm1 : m ∈ BBcard A n := Nat.find_spec hBBcard
    have hm2 : ∀ k, k ∈ BBcard A n → m ≤ k := by
      intro k hk
      exact Nat.find_min' hBBcard hk
    rw [Set.mem_setOf] at hm1
    obtain ⟨Bm, ⟨hBm1,hBm2⟩⟩ := hm1
    use Bm
    rw [Set.mem_setOf]
    constructor
    exact hBm1
    intro B1 hB1
    rw [hBm2]
    apply hm2
    rw [Set.mem_setOf]
    use B1
  have P (n : ℕ) : ∃ A B : ℕ → Finset α, B ∈ BB A n ∧ ∀ B2 ∈ BB A n, (B n).card ≤ (B2 n).card := by
    induction n with
      |zero =>
        use A
        rw [wellQuasiOrderedLE_def] at h
        unfold WellQuasiOrdered at h
        have hBB := isEmpty_or_nonempty (BB A 0)
        cases' hBB with Mty noMty
        · simp at Mty
          unfold BB at Mty
          simp at Mty
          have hMty : ∀ B : ℕ → Finset α, ¬ (∀ i j : ℕ, i < j → ¬ B i ⊆ B j) := by
            simpa [Set.ext_iff] using Mty
          simp at hMty

          intro B2 hB2
          rw [Set.mem_empty_iff_false] at hB2
          contradiction
        · specialize hBBmin A 0 noMty
          rw [Set.nonempty_coe_sort,Set.nonempty_def] at hBBmin
          obtain ⟨B,hB⟩ := hBBmin
          use B
          constructor
          grind
          intro B1 hB1
          grind
      |succ n Hn=>
        obtain ⟨A,⟨B,hAB⟩⟩ := Hn

        sorry
  sorry

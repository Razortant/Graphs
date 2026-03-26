import Mathlib
import Graphs.Ramsey

open Classical

variable {α : Type*} [Preorder α]

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

infix:50 " ≼ " => FinsetLE

def FinsetLT (s t : Finset α) : Prop := s ≼ t ∧ ¬ (t ≼ s)

def Bad (B : ℕ → Finset α) : Prop := ∀ i j, i < j → ¬ ((B i) ≼ (B j))

def Prefix {n : ℕ} (A : Fin n → Finset α) (B : ℕ → Finset α) : Prop := ∀ i, A i = B i

def BadPrefix {n : ℕ} (A : Fin n → Finset α) : Prop := ∃ B : ℕ → Finset α, (Bad B) ∧ (Prefix A B)

def Minima (A : Finset α) (AA : Set (Finset α)) : Prop := A ∈ AA ∧ ∀ A2 ∈ AA, A2 ≼ A → A ≼ A2

def Concat {n : ℕ} (A : Fin n → Finset α) (M : Finset α) : Fin (n + 1) → Finset α := by
  intro i
  by_cases h : i < n
  · exact A ⟨i, h⟩
  · exact M

lemma WFF (h : WellQuasiOrderedLE α) : WellFounded (FinsetLT (α := α)) := by
  have h2 : WellFounded (LT.lt (α := α)) := wellFounded_lt
  rw [wellFounded_iff_isEmpty_descending_chain,isEmpty_iff]
  intro ⟨f,hf⟩
  unfold FinsetLT at hf
  -- specialize hf n
  -- have ⟨hf1,hf2⟩ := hf
  -- unfold FinsetLE at hf1
  -- obtain ⟨g,hg⟩ := hf1
  -- rw [wellFounded_iff_isEmpty_descending_chain,isEmpty_iff] at h2
  -- simp at h2
  choose hf1 hf2 using hf
  apply hf2
  sorry
  sorry

-- Lemma 12.1.3
theorem Higman (h : WellQuasiOrderedLE α) : WellQuasiOrdered (FinsetLE (α := α)) := by
  have WFF : WellFounded (FinsetLT (α := α)) := WFF h
  contrapose h
  simp only [WellQuasiOrdered] at h
  push_neg at h
  obtain ⟨A,hA⟩ := h
  have P (n : ℕ) : ∀ A : Fin n → Finset α, BadPrefix A → ∃ M : Finset α, Minima M {M' : Finset α|BadPrefix (Concat A M')} := by
    intro A' hBPA'
    unfold BadPrefix at hBPA'
    obtain ⟨B,⟨hBBad,hA'PrefB⟩⟩ := hBPA'
    let BB := {M' | BadPrefix (Concat A' M')}
    have NptyBB : BB.Nonempty := by
      rw [Set.nonempty_def]
      use B n
      unfold BB
      rw [Set.mem_setOf]
      unfold BadPrefix
      use B
      constructor
      assumption
      unfold Prefix
      intro i
      unfold Concat
      by_cases h : i < n
      · simp [h]
        unfold Prefix at hA'PrefB
        exact hA'PrefB ⟨i,h⟩
      · simp [h]
        simp at h
        have h2 : i = n := by grind
        rw [h2]
    rw [WellFounded.wellFounded_iff_has_min] at WFF
    specialize WFF BB NptyBB
    obtain ⟨M,⟨hM1,hM2⟩⟩ := WFF
    have hM2' := hM2
    unfold FinsetLT at hM2
    push_neg at hM2
    use M
    unfold Minima
    constructor
    unfold BB at hM1
    assumption

    sorry
  have P0 := P 0
  simp [BadPrefix,Prefix,Concat] at P0
  specialize P0 A
  have h3 : Bad A := by
    unfold Bad
    assumption
  specialize P0 h3
  obtain ⟨A0,hA0⟩ := P0
  unfold Minima at hA0
  have ⟨hA0a,hA0b⟩ := hA0
  rw [Set.mem_setOf] at hA0a
  obtain ⟨B,⟨hBa,hBb⟩⟩ := hA0a
  sorry

-- theorem Higman (h : WellQuasiOrderedLE α) : WellQuasiOrdered (FinsetLE (α := α)) := by
--   by_contra h1
--   unfold WellQuasiOrdered at h1
--   simp at h1
--   obtain ⟨A,hA⟩ := h1
--   unfold FinsetLE at hA
--   simp at hA
--   let BB (A : ℕ → Finset α) (n : ℕ) := {B : ℕ → Finset α | (∀ i j : ℕ, i<j → ¬ B i ≤ B j) ∧ (∀ i < n, A i = B i)}
--   let BBcard (A : ℕ → Finset α) (n : ℕ) := {i : ℕ | ∃ B : ℕ → Finset α, B ∈ BB A n ∧ (B n).card = i}
--   let BBmin (A : ℕ → Finset α) (n : ℕ) := {B ∈ BB A n | ∀ B1 ∈ BB A n, (B n).card ≤ (B1 n).card}
--   have hBBmin (A : ℕ → Finset α) (n : ℕ) : Nonempty (BB A n) → Nonempty (BBmin A n) := by
--     intro hBB
--     obtain ⟨B, hB⟩ := hBB
--     have hcard : (B n).card ∈ BBcard A n := by
--       rw [Set.mem_setOf]
--       use B
--     let Bcard := (B n).card
--     rw [Set.nonempty_coe_sort,Set.nonempty_def]
--     have hBBcard : ∃ i, i ∈ BBcard A n := by use (B n).card
--     let m := Nat.find hBBcard
--     have hm1 : m ∈ BBcard A n := Nat.find_spec hBBcard
--     have hm2 : ∀ k, k ∈ BBcard A n → m ≤ k := by
--       intro k hk
--       exact Nat.find_min' hBBcard hk
--     rw [Set.mem_setOf] at hm1
--     obtain ⟨Bm, ⟨hBm1,hBm2⟩⟩ := hm1
--     use Bm
--     rw [Set.mem_setOf]
--     constructor
--     exact hBm1
--     intro B1 hB1
--     rw [hBm2]
--     apply hm2
--     rw [Set.mem_setOf]
--     use B1
--   have P (n : ℕ) : ∃ A B : ℕ → Finset α, B ∈ BB A n ∧ ∀ B2 ∈ BB A n, (B n).card ≤ (B2 n).card := by
--     induction n with
--       |zero =>
--         use A
--         rw [wellQuasiOrderedLE_def] at h
--         unfold WellQuasiOrdered at h
--         have hBB := isEmpty_or_nonempty (BB A 0)
--         cases' hBB with Mty noMty
--         · suffices: A ∈ BB A 0
--           · simp at Mty
--             rw [Mty] at this
--             contradiction
--           simp [BB]
--           intro i j hij hh
--           specialize hA i j hij
--           let f : (A i) ↪ (A j) := by
--             refine ⟨fun x => ⟨x, hh x.prop⟩, ?_⟩
--             intro a b
--             simp
--           specialize hA f
--           obtain ⟨x0, hx0, hx0'⟩ := hA
--           simp [f] at hx0'
--         · specialize hBBmin A 0 noMty
--           rw [Set.nonempty_coe_sort,Set.nonempty_def] at hBBmin
--           obtain ⟨B,hB⟩ := hBBmin
--           use B
--           constructor
--           grind
--           intro B1 hB1
--           grind
--       |succ n Hn =>
--         obtain ⟨An,⟨Bn,⟨hn1,hn2⟩⟩⟩ := Hn
--         have noMty : Nonempty (BB An n) := by
--           rw [Set.nonempty_coe_sort,Set.nonempty_def]
--           use Bn
--         apply hBBmin An at noMty
--         obtain ⟨An',hAn'⟩ := noMty
--         have : Nonempty (BBmin An' (n + 1)) := by sorry
--         obtain ⟨B',hB'⟩ := this
--         let A2 (i : ℕ) : Finset α := if i = n + 1 then B' i else An' i
--         use A2
--         use B'
--         constructor
--         rw [Set.mem_setOf]
--         constructor
--         rw [Set.mem_setOf] at hB'
--         have hB' := hB'.left
--         rw [Set.mem_setOf] at hB'
--         have hB' := hB'.left
--         exact hB'
--         intro i hi
--         by_cases hi2 : i = n + 1
--         grind
--         grind
--         rw [Set.mem_setOf] at hB'
--         have hB' := hB'.right
--         intro B2 hB2
--         specialize hB' B2
--         rw [Set.mem_setOf] at hB2
--         have: B2 ∈ BB An' (n + 1) := by
--           rw [Set.mem_setOf]
--           constructor
--           grind
--           grind
--         specialize hB' this
--         assumption
--   -- Need P = ∃ A, ∀ (n : ℕ), ∃ B ∈ BB A n, ∀ B2 ∈ BB A n, (B n).card ≤ (B2 n).card
--   sorry

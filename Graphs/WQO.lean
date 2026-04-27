import Mathlib
import Graphs.Ramsey

noncomputable section

open Classical

variable {α : Type*} [Preorder α]

theorem QO_tricolor {X : Type*} [Preorder X] (f : ℕ → X) : ∃ g : ℕ ↪o ℕ, (Monotone (f ∘ g) ∨ StrictAnti (f ∘ g) ∨ (∀ i : ℕ, ∀ j : ℕ, i < j → ¬ ((f (g i) ≤ f (g j)) ∨ (f (g i) > f (g j))))) := by
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

theorem FinsetLE_trans {s t u : Finset α} : s ≼ t → t ≼ u → s ≼ u := by
  unfold FinsetLE
  intro hst htu
  obtain ⟨f,hf⟩ := hst
  obtain ⟨g,hg⟩ := htu
  use Function.Embedding.trans f g
  intro x
  simp only [Function.Embedding.trans_apply]
  specialize hg (f x)
  specialize hf x
  exact LE.le.trans hf hg

def FinsetLT (s t : Finset α) : Prop := s ≼ t ∧ ¬ (t ≼ s)

def Bad (B : ℕ → Finset α) : Prop := ∀ i j, i < j → ¬ ((B i) ≼ (B j))

def Prefix {n : ℕ} (A : Fin n → Finset α) (B : ℕ → Finset α) : Prop := ∀ i, A i = B i

def BadPrefix {n : ℕ} (A : Fin n → Finset α) : Prop := ∃ B : ℕ → Finset α, (Bad B) ∧ (Prefix A B)

def Minima (A : Finset α) (AA : Set (Finset α)) : Prop := A ∈ AA ∧ ∀ A2 ∈ AA, A2 ≼ A → A ≼ A2

def MinimaCard (A : Finset α) (AA : Set (Finset α)) : Prop := A ∈ AA ∧ ∀ A2 ∈ AA, A.card ≤ A2.card

def BadMini (A : ℕ → Finset α) (AA : Set (Finset α)) : Prop := Bad A ∧ ∀ n : ℕ, MinimaCard (A n) AA

def toPref (n : ℕ) (A : ℕ → Finset α) : Fin n → Finset α := fun n ↦ A n

def localProp (P : (ℕ → α) → Prop) := ∀ ⦃f⦄, (∀ n, ∃ g, P g ∧ ∀ k < n, g k = f k) → P f

def PrevPrefix {n : ℕ} (A : Fin (n+1) → Finset α) : Fin n → Finset α :=
  fun i => A ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self n)⟩

def Concat {n : ℕ} (A : Fin n → Finset α) (M : Finset α) : Fin (n + 1) → Finset α := by
  intro i
  by_cases h : i < n
  · exact A ⟨i, h⟩
  · exact M

lemma PrevConcat {n : ℕ} (A : Fin n → Finset α) (M : Finset α) : PrevPrefix (Concat A M) = A := by
  unfold PrevPrefix Concat
  simp only [Fin.is_lt, ↓reduceDIte, Fin.eta]

def ge_of_gt : ∀ a b : α, a > b → a ≥ b := by
            intro a' b' ha'b'
            change b' ≤ a'
            apply le_of_lt
            assumption

-- lemma WFF (h : WellQuasiOrderedLE α) : WellFounded (FinsetLT (α := α)) := by
--   have h2 : WellFounded (LT.lt (α := α)) := wellFounded_lt
--   rw [wellFounded_iff_isEmpty_descending_chain,isEmpty_iff]
--   intro ⟨f,hf⟩
--   unfold FinsetLT at hf
--   -- specialize hf n
--   -- have ⟨hf1,hf2⟩ := hf
--   -- unfold FinsetLE at hf1
--   -- obtain ⟨g,hg⟩ := hf1
--   -- rw [wellFounded_iff_isEmpty_descending_chain,isEmpty_iff] at h2
--   -- simp at h2
--   choose hf1 hf2 using hf
--   unfold FinsetLE at hf1 hf2
--   push_neg at hf2

--   sorry

set_option maxHeartbeats 400000 in

-- Lemma 12.1.3
theorem Higman (h : WellQuasiOrderedLE α) : WellQuasiOrdered (FinsetLE (α := α)) := by
  -- have WFF : WellFounded (FinsetLT (α := α)) := WFF h
  contrapose h
  simp only [WellQuasiOrdered] at h
  push_neg at h
  obtain ⟨A,hA⟩ := h
  have P (n : ℕ) : ∀ A : Fin n → Finset α, BadPrefix A → ∃ M : Finset α, MinimaCard M {M' : Finset α|BadPrefix (Concat A M')} := by
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
    let BBcard := {i : ℕ | ∃ B ∈ BB, B.card = i}
    let BBmin := {B| MinimaCard B BB}
    have hBBmin : BB.Nonempty → BBmin.Nonempty := by
      intro hBB
      obtain ⟨B, hB⟩ := hBB
      have hcard : B.card ∈ BBcard := by grind only [usr Set.mem_setOf_eq]
      rw [Set.nonempty_def]
      have hBBcard : ∃ i, i ∈ BBcard := by use B.card
      let m := Nat.find hBBcard
      have hm1 : m ∈ BBcard := Nat.find_spec hBBcard
      have hm2 : ∀ k, k ∈ BBcard → m ≤ k := by
        intro k hk
        exact Nat.find_min' hBBcard hk
      rw [Set.mem_setOf] at hm1
      obtain ⟨Bm, ⟨hBm1,hBm2⟩⟩ := hm1
      use Bm
      rw [Set.mem_setOf]
      constructor
      assumption
      intro A2 hA2
      rw [hBm2]
      apply hm2
      grind only [usr Set.mem_setOf_eq]
    specialize hBBmin NptyBB
    obtain ⟨M,hM⟩ := hBBmin
    use M
    assumption
    -- rw [WellFounded.wellFounded_iff_has_min] at WFF
    -- specialize WFF BB NptyBB
    -- obtain ⟨M,⟨hM1,hM2⟩⟩ := WFF
    -- have hM2' := hM2
    -- unfold FinsetLT at hM2
    -- push_neg at hM2
    -- use M
    -- unfold Minima
    -- constructor
    -- unfold BB at hM1
    -- assumption
    -- intro A2 hA2
    -- specialize hM2 A2
    -- unfold BB at hM2
    -- apply hM2
    -- assumption

  have P0 := P 0
  simp [BadPrefix,Prefix,Concat] at P0
  specialize P0 A
  have h3 : Bad A := by
    unfold Bad
    assumption
  specialize P0 h3
  obtain ⟨A0,hA0⟩ := P0
  unfold MinimaCard at hA0
  have ⟨hA0a,hA0b⟩ := hA0
  rw [Set.mem_setOf] at hA0a
  obtain ⟨B,⟨hBa,hBb⟩⟩ := hA0a
  let Amin (n : ℕ) : {f : Fin (n + 1) → Finset α // BadPrefix f ∧ MinimaCard (f ⟨n, by omega⟩) {M' | BadPrefix (Concat (PrevPrefix f) M')}} := by
    induction n with
      |zero =>
        let fA0 := fun (1 : Fin (0 + 1)) ↦ A0
        have hfA0 : BadPrefix fA0 ∧ MinimaCard (fA0 ⟨0, by omega⟩) {M' | BadPrefix (Concat (PrevPrefix fA0) M')}:= by
          simp [BadPrefix,Prefix]
          constructor
          use B
          unfold MinimaCard
          constructor
          grind only
          grind only
        exact ⟨fA0,hfA0⟩
      |succ n hn =>
        refine ⟨Concat hn ((P (n+1) hn.1 hn.2.1).choose), ?_⟩
        obtain ⟨f,⟨hf1,hf2⟩⟩ := hn
        have hf' := P (n+1) f hf1
        let M := hf'.choose
        have hM := hf'.choose_spec
        let f2 := Concat f M
        have res : BadPrefix f2 ∧ MinimaCard (f2 ⟨n + 1, by omega⟩) {M' | BadPrefix (Concat (PrevPrefix f2) M')} := by
          have ⟨hM1,hM2⟩ := hM
          rw [Set.mem_setOf] at hM1
          constructor
          assumption
          constructor
          rw [Set.mem_setOf]
          unfold f2
          rw [PrevConcat]
          have this : Concat f M ⟨n + 1, by omega⟩ = M := by
            unfold Concat
            simp only [lt_self_iff_false, ↓reduceDIte]
          rw [this]
          assumption
          intro A2 hA2
          unfold f2
          unfold Concat
          simp only [lt_self_iff_false, ↓reduceDIte]
          apply hM2
          unfold f2 at hA2
          rw [PrevConcat] at hA2
          assumption
        exact res
  have eqgen : ∀ i' j' : ℕ, (hi'j' : i' ≤ j') → ∀ l, (hli' : l ≤ i') → (Amin i').1 ⟨l,by omega⟩ = (Amin j').1 ⟨l,by omega⟩ := by
    intro i' j' hi'j' l hli'
    obtain ⟨k,⟨hk1,hk2⟩⟩ := (le_iff_exists_add).mp hi'j'
    induction k with
      | zero =>
        unfold Amin
        grind only
      | succ k hreck =>
        have hi'k : i' ≤ i' + k := by omega
        specialize hreck hi'k
        rw [hreck]
        have hassoc : i' + (k + 1) = (i' + k) + 1 := Nat.add_assoc i' k 1
        -- subst hassoc
        -- unfold Amin
        change (Amin (i' + k)).1 ⟨l, _⟩ = (Amin (i' + k + 1)).1 ⟨l, _⟩
        have : ∀ n, ∃ M, (Amin (n + 1)).1 = Concat (Amin n) M := by grind
        obtain ⟨M,hM⟩ := this (i' + k)
        rw [hM]
        simp [Concat]
        omega
  let Amin' (n : ℕ) : Finset α := (Amin n).1 ⟨n, by omega⟩
  have hBA : Bad Amin' := by
    unfold Bad
    by_contra absurd
    push_neg at absurd
    obtain ⟨i,temp⟩ := absurd
    obtain ⟨j,⟨hij1,hij2⟩⟩ := temp
    unfold Amin' at hij2
    have hAmin (i : ℕ) := (Amin i).2
    suffices eq : (Amin i).1 ⟨i, by omega⟩ = (Amin j).1 ⟨i, by omega⟩ by
      · have ⟨hAminj1,hAminj2⟩ := hAmin j
        unfold BadPrefix at hAminj1
        obtain ⟨B2,⟨hB2a,hB2b⟩⟩ := hAminj1
        unfold Prefix at hB2b
        unfold Bad at hB2a
        specialize hB2a i j hij1
        rw [← hB2b ⟨i, by omega⟩, ← hB2b ⟨j, by omega⟩, ← eq] at hB2a
        contradiction
    exact eqgen i j (le_of_lt hij1) i (by omega)
  have noMty : ∀ n : ℕ, (Amin' n).Nonempty := by
    intro n
    by_contra Mpty
    simp only [Finset.not_nonempty_iff_eq_empty] at Mpty
    unfold Bad at hBA
    specialize hBA n (n+1) (by omega)
    rw [Mpty] at hBA
    unfold FinsetLE at hBA
    simp at hBA
  let a (n : ℕ) : α := (noMty n).choose
  let Bmin (n : ℕ) : Finset α := (Amin' n) \ {a n}
  by_contra WQOLEα
  have hIISS : ∃ g : ℕ ↪o ℕ, Monotone (a ∘ g) := by
    have trico := QO_tricolor a
    obtain ⟨g,hg⟩ := trico
    rw [wellQuasiOrderedLE_iff] at WQOLEα
    have ⟨WF,anti⟩ := WQOLEα
    cases' hg with hg1 hg2
    use g
    cases' hg2 with hg2 hg3
    · unfold StrictAnti at hg2
      simp only [Function.comp_apply] at hg2
      have WF : WellFounded ((· < ·) : α → α → Prop) := WF.wf
      rw [wellFounded_iff_isEmpty_descending_chain,isEmpty_iff] at WF
      simp only [Subtype.forall,imp_false, not_forall] at WF
      specialize WF (a ∘ g)
      obtain ⟨x,hx⟩ := WF
      specialize hg2 (Nat.lt_succ_self x)
      contradiction
    · let s := {a (g n) | n : ℕ}
      specialize anti s
      have anti' : IsAntichain (fun x1 x2 ↦ x1 ≤ x2) s := by
        change s.Pairwise (fun x1 x2 ↦ x1 ≤ x2)ᶜ
        change ∀ ⦃x : α⦄, x ∈ s → ∀ ⦃y : α⦄, y ∈ s → x ≠ y → (fun x1 x2 ↦ x1 ≤ x2)ᶜ x y
        intro x hx y hy hxy
        simp only [Pi.compl_apply, compl_iff_not]
        rw [Set.mem_setOf] at hx hy
        obtain ⟨i, hi⟩ := hx
        obtain ⟨j, hj⟩ := hy
        rw [← hi,← hj] at ⊢ hxy
        by_cases P : i = j
        rw [P] at hxy
        contradiction
        push_neg at P
        rw [Nat.lt_or_gt] at P
        cases' P with P1 P2
        · specialize hg3 i j P1
          push_neg at hg3
          exact hg3.left
        · specialize hg3 j i P2
          simp only [gt_iff_lt, not_or] at hg3
          have ⟨hg3l,hg3r⟩ := hg3
          intro h
          apply hg3r
          exact lt_of_le_not_ge h hg3l
      specialize anti anti'
      unfold s at anti
      have := @Finite.exists_infinite_fiber ℕ {x | ∃ n, a (g n) = x} _ (Set.finite_coe_iff.mpr anti)
        (fun n => ⟨a (g n), by { simp }⟩)
      obtain ⟨y, hS⟩ := this
      let S' : Set ℕ := ((fun n ↦ ⟨a (g n), by simp⟩) ⁻¹' {y})
      have hS' : S'.Infinite := Set.infinite_coe_iff.mp hS
      let G := @Nat.orderEmbeddingOfSet S' hS _
      have : ∀ n, a (g (G n)) = y := by
        intro n
        have : G n ∈ S' := by simp [G]
        simp [S'] at this
        grind
      refine ⟨G.trans g, ?_⟩
      intro i j hij
      simp [this]
  obtain ⟨n,hn⟩ := hIISS
  let U (i : ℕ) : Finset α := if i < n 0 then Amin' i else Bmin (n (i - n 0))
  have hU : ¬ Bad U := by
    let An := Amin (n 0)
    have An1 := An.2.1
    have An2 := An.2.2
    simp [An] at An1 An2
    let Upref : Fin (n 0 + 1) → Finset α := toPref (n 0 + 1) U
    suffices hBPU : ¬ BadPrefix Upref
    · unfold BadPrefix at hBPU
      push_neg at hBPU
      intro hBU
      specialize hBPU U hBU
      apply hBPU
      unfold Prefix Upref toPref
      simp only [implies_true]
    let f := PrevPrefix Upref
    intro hBPU
    have hUnMin : Upref ⟨n 0, by omega⟩ ∈ {M' | BadPrefix (Concat (f) M')} := by
      rw [Set.mem_setOf]
      have : ∀ i, Upref i = Concat f (Upref ⟨n 0, by omega⟩) i := by
        unfold f PrevPrefix Concat
        intro ⟨i,hi⟩
        simp only [left_eq_dite_iff, not_lt]
        intro h
        replace h : i = n 0 := by omega
        simp [h]
      have : Upref = Concat f (Upref ⟨n 0, by omega⟩) := by
        apply funext
        intro i
        exact Finset.val_inj.mp (congrArg Finset.val (this i))
      exact cast (congrArg BadPrefix this) hBPU
    let g := toPref (n 0 + 1) Amin'
    have : BadPrefix g ∧ MinimaCard (g ⟨n 0, by omega⟩) {M' | BadPrefix (Concat (PrevPrefix g) M')} := by
      constructor
      · use Amin'
        constructor
        assumption
        unfold g toPref Prefix
        simp only [implies_true]
      · constructor
        rw [Set.mem_setOf]
        unfold BadPrefix
        use Amin'
        constructor
        · assumption
        · unfold g PrevPrefix Concat Prefix toPref
          simp only [dite_eq_ite, ite_eq_left_iff, not_lt]
          intro ⟨i,hi⟩ h
          simp only at h
          replace h : i = n 0 := by omega
          simp [h]
        exfalso
        unfold MinimaCard at An2
        have := An2.2
        unfold f at hUnMin
        have toto : PrevPrefix Upref = (PrevPrefix ↑(Amin (n 0))) := by
          ext1 i
          simp [Upref, U, toPref, PrevPrefix, Amin']
          grind
        rw [toto] at hUnMin
        specialize this (Upref ⟨n 0, by omega⟩)
        simp [hUnMin] at this
        have titi : n 0 - n 0 = 0 := by simp
        simp [Upref, toPref, U, Bmin, Amin'] at this
        have this2 : (Amin (n (n 0 - n 0))).1 ⟨n 0, by simp⟩ = ((Amin (n 0)).1 ⟨n 0, by omega⟩) := by grind only
        rw [this2] at this
        replace this : (Amin (n 0)).1 ⟨n 0, by omega⟩ ⊂ (Amin (n 0)).1 ⟨n 0, by omega⟩ \ {a (n 0)} := by grind
        apply Finset.card_lt_card at this
        grind
    have ⟨hBFg,hMCg1,hMCg2⟩ := this
    have : PrevPrefix g = f := by
      unfold g f Upref toPref PrevPrefix U
      simp
    rw [this] at hMCg1 hMCg2
    specialize hMCg2 (Upref ⟨n 0,_⟩) hUnMin
    unfold g Upref toPref U Bmin at hMCg2
    simp at hMCg2
    grind
  unfold Bad at hU
  push_neg at hU
  obtain ⟨i,j,hij1,hij2⟩ := hU
  unfold U at hij2
  unfold Bad at hBA
  by_cases Pi : i < n 0
  by_cases Pj : j < n 0
  · simp [Pi, Pj] at hij2
    exact Ne.elim (fun a ↦ hBA i j hij1 hij2) hBb
  · simp [Pi, Pj] at hij2
    have : Bmin (n (j - n 0)) ≼ Amin' (n (j - n 0)) := by
      unfold Bmin FinsetLE
      let f (x : ↥(Amin' (n (j - n 0)) \ {a (n (j - n 0))})) : ↥(Amin' (n (j - n 0))) := by
        obtain ⟨x,hx⟩ := x
        have : x ∈ Amin' (n (j - n 0)) := by grind
        exact ⟨x,this⟩
      refine ⟨⟨?_,?_⟩,?_⟩
      exact f
      unfold Function.Injective
      intro a1 a2 ha1a2
      simp [f] at ha1a2
      exact ha1a2
      intro ⟨x,hx⟩
      simp only [Function.Embedding.coeFn_mk, ge_iff_le]
      unfold f
      simp only [le_refl]
    have this2 := FinsetLE_trans hij2 this
    specialize hBA i (n (j - n 0))
    apply hBA
    have this3 : n 0 ≤ n (j - n 0) := by
      rw [OrderEmbedding.le_iff_le]
      exact Nat.zero_le (j - n 0)
    apply Nat.lt_of_lt_of_le Pi this3
    assumption
  by_cases Pj : j < n 0
  · apply Pi
    omega
  · simp [Pi, Pj] at hij2
    obtain ⟨f,hf⟩ := hij2
    let f2 (x : Amin' (n (i - n 0))) : Amin' (n (j - n 0)) := by
      obtain ⟨x,hx⟩ := x
      by_cases Px : x ∈ Bmin (n (i - n 0))
      · specialize hf ⟨x,Px⟩
        simp only at hf
        refine ⟨?_,?_⟩
        exact ↑(f ⟨x, Px⟩)
        have hBsbA : Bmin (n (j - n 0)) ⊆ Amin' (n (j - n 0)) := by
          unfold Bmin
          exact Finset.sdiff_subset
        apply hBsbA
        exact Finset.coe_mem (f ⟨x, Px⟩)
      · unfold Bmin at Px
        have : x = a (n (i - n 0)) := by
          simp only [Finset.mem_sdiff, Finset.mem_singleton, not_and, Decidable.not_not] at Px
          exact (Px ∘ fun a ↦ hx) α
        refine ⟨?_,?_⟩
        exact a (n (j - n 0))
        exact (noMty (n (j - n 0))).choose_spec
    have : Amin' (n (i - n 0)) ≼ Amin' (n (j - n 0)) := by
      refine ⟨⟨?_,?_⟩,?_⟩
      exact f2
      unfold Function.Injective
      intro a1 a2 ha1a2
      unfold f2 at ha1a2
      simp at ha1a2
      by_cases Pa1 : ↑a1 ∈ Bmin (n (i - n 0))
      by_cases Pa2 : ↑a2 ∈ Bmin (n (i - n 0))
      · simp [Pa1,Pa2] at ha1a2
        assumption
      · simp [Pa1,Pa2] at ha1a2
        have : ¬ a (n (j - n 0)) ∈ ↑(Bmin (n (j - n 0))) := by
          unfold Bmin
          intro h
          simp at h
        grind only
      by_cases Pa2 : ↑a2 ∈ Bmin (n (i - n 0))
      · simp [Pa1,Pa2] at ha1a2
        grind only [= Finset.mem_sdiff, usr Subtype.property, = Finset.mem_singleton]
      · grind only [= Finset.mem_sdiff, usr Subtype.property, = Finset.mem_singleton]
      intro ⟨x,hx⟩
      simp only [Function.Embedding.coeFn_mk, ge_iff_le]
      unfold f2
      by_cases Px : x ∈ Bmin (n (i - n 0))
      · simp [Px]
        exact le_of_le_of_eq'' (hf ⟨x, of_eq_true (eq_true Px)⟩) rfl
      · simp [Px]
        unfold Bmin at Px
        simp only [Finset.mem_sdiff, Finset.mem_singleton, not_and, Decidable.not_not] at Px
        apply Px at hx
        rw [hx]
        apply hn
        omega
    refine hBA _ _ ?_ this
    refine (OrderEmbedding.lt_iff_lt n).mpr ?_
    omega

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

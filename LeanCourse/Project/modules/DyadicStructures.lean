import Mathlib
open Function Set Classical
noncomputable section

/- ## Dyadic Structures -/
namespace DyadicStructures

/-- Definition 1.1: Dyadic Interval and dyadic rectangle
  A dyadic interval is defined as `[2^k * n, 2^k * (n + 1))`. --/
def dyadicInterval (k n : ℤ) : Set ℝ :=
  { x | (2^k : ℝ) * n ≤ x ∧ x < (2^k : ℝ) * (n + 1) }


--Check that 0.4 belongs to the dyadic interval `2^(-5) * 12, 2^(-5)*(12+1)`, i.e. `[0.37500, 0.40625)`.
example : (0.4 : ℝ) ∈ dyadicInterval (-5) 12 := by
  simp [dyadicInterval]
  norm_num

--Check that 0.75 does not belong to the dyadic interval `[0, 0.5) = dyadicInterval -1 0`.
example : (0.75 : ℝ) ∉ dyadicInterval (-1) 0 := by
  simp [dyadicInterval]
  norm_num


/-- A dyadic rectangle is the Cartesian product of two dyadic intervals. --/
def dyadicRectangle (k n k' n' : ℤ) : Set (ℝ × ℝ)  :=
  (dyadicInterval k n).prod (dyadicInterval k' n')

/-- Collection of dyadic intervals at a fixed scale.
  I DONT USE IT - MAYBE I SHOULD GET RID OF IT? --/
def SetDyadicIntervals (m : ℕ) : Set (Set ℝ) :=
  {dyadicInterval (-m) n | n ∈ Finset.range (2^m)}

/-- Theorem: Two dyadic intervals are either disjoint or one is contained in the other. --/
theorem dyadic_intervals_disjoint_or_contained (k k' n n' : ℤ) :
  (dyadicInterval k n ∩ dyadicInterval k' n' = ∅) ∨
  (dyadicInterval k n ⊆ dyadicInterval k' n') ∨
  (dyadicInterval k' n' ⊆ dyadicInterval k n) := by
  unfold dyadicInterval
  --they have the same length, so they may be the same interval or they are disjoint
  by_cases hk : k = k'
  rw[hk]
  -- they have the same length and the same beginning → they are the same
  by_cases hn : n = n'
  rw[hn]
  simp
  -- they have the same length and different beginning → they are disjoint
  left
  ext x
  rw [← Set.setOf_and]
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ -- deviding inequalities for different hypothesis
  by_cases hn1 : n< n'
  have h : n + 1 ≤ n' := by
    rw[Int.add_one_le_iff]
    apply hn1
  have h12 : (2 ^ k' : ℝ) * (↑n + 1) ≤ (2 ^ k' : ℝ) * ↑n' := by
    apply mul_le_mul_of_nonneg_left
    exact_mod_cast h
    linarith
  linarith
  --here the case  n' smaller than n beginns
  have h : n' + 1 ≤ n := by
    rw[Int.add_one_le_iff, ← Int.not_le, le_iff_eq_or_lt,not_or]
    exact Decidable.not_imp_iff_and_not.mp fun a ↦ hn1 (a hn)
  have h12 : (2 ^ k' : ℝ) * (↑n' + 1) ≤ (2 ^ k' : ℝ) * ↑n := by
    apply mul_le_mul_of_nonneg_left
    exact_mod_cast h
    linarith
  --they have different length, so the smaller one can be contained in another or they are disjoint
  linarith
  by_cases hk1 : k<k'
  by_cases hn1 : (2^k' *n' : ℝ ) ≤ n *2^k
  by_cases hn2 : ((n+1) * 2^k : ℝ ) ≤   2^k' * (n'+1)
  right
  left
  intros x h1
  rcases h1 with ⟨h_left, h_right⟩
  refine mem_setOf.mpr ?_
  have h_1 : 2 ^ k' * (n' : ℝ) ≤ x := by
    apply le_trans hn1
    rw [mul_comm]
    exact h_left
  have h_2 : x < 2 ^ k' * (↑n' + 1) := by
    apply lt_of_lt_of_le h_right
    rw [mul_comm]
    exact hn2
  apply And.intro
  exact h_1
  exact h_2
  left
  ext x
  rw [← Set.setOf_and]
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
 -- rw[← lt_of_not_le] at hn2
  rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ -- deviding inequalities for different hypothesis
  have h_10 : (2^k' : ℝ ) <2^k := by
    sorry
  sorry
  /-simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ -- deviding inequalities for different hypothesis
  have h_10 :  (2 ^ k' * (↑n'+1) : ℝ ) ≤ ↑n * 2 ^ k := by
    by_contra h
    rw[not_le] at hn2
    --rw[not_le] at h
    rw[← Int.add_one_le_iff] at hk1
    have A : (2 : ℝ) ^ k * (n : ℝ) ≤ (2 : ℝ) ^ k' * (n' + 1) := le_trans h1 (le_of_lt h4)--no to jest sprzeczne z h
    have B : (2 : ℝ) ^ k' * (n' : ℝ) ≤ (2 : ℝ) ^ k * (n + 1) := le_trans h3 (le_of_lt h2)
    sorry
  linarith-/
  left
  ext x
  rw [← Set.setOf_and]
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ -- deviding inequalities for different hypothesis
  have h_10 :  (2 ^ k * (↑n+1) : ℝ ) ≤ ↑n' * 2 ^ k' := by
    sorry
  linarith
  by_cases hn1 : (2^k' *n' : ℝ ) ≤ n *2^k
  by_cases hn2 : ((n+1) * 2^k : ℝ ) ≤   2^k' * (n'+1)
  right
  left
  intros x h1
  rcases h1 with ⟨h_left, h_right⟩
  refine mem_setOf.mpr ?_
  have h_1 : 2 ^ k' * (n' : ℝ) ≤ x := by
    apply le_trans hn1
    rw [mul_comm]
    exact h_left
  have h_2 : x < 2 ^ k' * (↑n' + 1) := by
    apply lt_of_lt_of_le h_right
    rw [mul_comm]
    exact hn2
  apply And.intro
  exact h_1
  exact h_2
  left
  ext x
  rw [← Set.setOf_and]
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ -- deviding inequalities for different hypothesis
  have h_10 :  (2 ^ k' * (↑n'+1) : ℝ ) ≤ ↑n * 2 ^ k := by
    sorry
  linarith
  left
  ext x
  rw [← Set.setOf_and]
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ -- deviding inequalities for different hypothesis
  have h_10 :  (2 ^ k * (↑n+1) : ℝ ) ≤ ↑n' * 2 ^ k' := by
    sorry
  linarith



theorem mul_pow_inequality { k k' n n' : ℕ }
  (h : n < n') (h' : k < k') : (2^k : ℝ) * (n+1)  < 2^k' * n'  := by
  rw [← n.add_one_le_iff] at h
  have h0 : 2^k < 2^k' := by
    refine (pow_lt_pow_iff_right ?h).mpr h'
    linarith
  --apply Nat.mul_lt_mul_of_lt_of_le h0 h
  sorry

--case for k smaller and n smaller, both natural
theorem dyadic_intervals_disjoint_or_contained1 (k k' n n' : ℕ ) (h : k < k'):
  (dyadicInterval k n ∩ dyadicInterval k' n' = ∅) ∨
  (dyadicInterval k n ⊆ dyadicInterval k' n') ∨
  (dyadicInterval k' n' ⊆ dyadicInterval k n) := by
  -- Unfold the definition to make the intervals visible.
  unfold dyadicInterval
  by_cases h1 : n<n'
  left
  ext x
  rw [← Set.setOf_and]
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
 -- apply mul_pow_inequality at h h1

  sorry
  sorry


/- Definition 1.2: Tile-/
def Tile (I : Set ℝ) (ω : Set ℝ) : Prop :=
  ∃ k n : ℤ, I = dyadicInterval k n ∧ ω = {x | x = 2^(-k)}

-- Definition 1.3: Dyadic Test Function
-- (Left for a future fix if needed.)
/-
def dyadicTestFunction (N : ℕ) (coeffs : Fin N → ℝ) (intervals : Fin N → Set ℝ) : ℝ → ℝ :=
  λ x => ∑ k , ∑ n , coeffs k * (dyadicInterval k n).indicator 1 x
-/

end DyadicStructures

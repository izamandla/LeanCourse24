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


/-- A dyadic interval can be split into two smaller dyadic intervals. --/
lemma dyadicInterval_split (k n : ℤ) :
  dyadicInterval k n = dyadicInterval (k - 1) (2 * n) ∪ dyadicInterval (k - 1) (2 * n + 1) := by
  ext x
  simp[dyadicInterval]
  have h1 : (2 : ℝ ) ^ (k - 1) * 2 = 2 ^ k := by
    rw[ ← pow_one 2, /-← zpow_mul 2 1 (k-1)-/]
    sorry
  constructor
  intro h
  obtain ⟨h_1, h_2⟩ := h
  constructor
  constructor
  rw[← mul_assoc]
  rw[h1]
  apply h_1
  rw[mul_add]
  sorry
  sorry

theorem dyadicInterval_disjoint_help {k n n' : ℤ} (h : n < n') :
  (dyadicInterval k n ∩ dyadicInterval k n') = ∅ := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
  have h0 : n + 1 ≤ n' := by
    rw[Int.add_one_le_iff]
    apply h
  have h12 : (2 ^ k : ℝ) * (n + 1) ≤ (2 ^ k : ℝ) * n' := by
    apply mul_le_mul_of_nonneg_left
    exact_mod_cast h0
    linarith
  linarith

  theorem dyadicInterval_disjoint (k n n' : ℤ) (h : n ≠ n') :
  (dyadicInterval k n ∩ dyadicInterval k n') = ∅ := by
  by_cases h1 : n<n'
  apply dyadicInterval_disjoint_help
  apply h1
  push_neg at h1
  have h1' : n' < n := by
    exact lt_of_le_of_ne h1 (id (Ne.symm h))
  rw[Set.inter_comm]
  apply dyadicInterval_disjoint_help
  apply h1'


theorem dyadicInterval_cover (k : ℤ) :
  ⋃ n : ℤ, dyadicInterval k n = Set.univ := by
  ext x
  simp [dyadicInterval]
  let n := Int.floor (x / (2^k : ℝ))
  have h1 :  2^k* n ≤ x := by
    simp[n]
    ring_nf
    have : (⌊x / (2^k : ℝ)⌋ : ℝ) ≤ x / (2^k : ℝ) := Int.floor_le (x / (2^k : ℝ))
    rw[mul_comm,← le_div_iff₀]
    exact this
    refine zpow_pos_of_pos ?ha k
    linarith
  have h2 : x < 2^k * (n+1) := by
    unfold n
    have : x / (2^k : ℝ) < (⌊x / (2^k : ℝ)⌋ + 1 : ℝ) := Int.lt_floor_add_one (x / (2^k : ℝ))
    rw[mul_comm, ← div_lt_iff₀]
    exact this
    refine zpow_pos_of_pos ?ha k
  exact Filter.frequently_principal.mp fun a ↦ a h1 h2

theorem dyadicInterval_length (k n : ℤ) (x y : ℝ ) (h : x ∈ dyadicInterval k n ∧ y ∈ dyadicInterval k n) : |x - y| ≤ (2^k : ℝ) := by
  simp [dyadicInterval] at h
  rw[abs_sub_le_iff]
  constructor
  simp
  linarith
  simp
  linarith




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



/-theorem mul_pow_inequality { k k' n n' : ℕ }
  (h : n < n') (h' : k < k') : (2^k : ℝ) * (n+1)  < 2^k' * n'  := by
  rw [← n.add_one_le_iff] at h
  have h0 : 2^k < 2^k' := by
    refine (pow_lt_pow_iff_right ?h).mpr h'
    linarith
  --apply Nat.mul_lt_mul_of_lt_of_le h0 h
  sorry-/

--case for k smaller and n smaller, both natural
theorem dyadic_intervals_disjoint_or_contained1 (k k' n n' : ℕ ) (h : k < k'):
  (dyadicInterval k n ∩ dyadicInterval k' n' = ∅) ∨
  (dyadicInterval k n ⊆ dyadicInterval k' n') ∨
  (dyadicInterval k' n' ⊆ dyadicInterval k n) := by
  -- Unfold the definition to make the intervals visible.
  unfold dyadicInterval
  -- n is smaller than n' so they are disjoint bc 2^k * n is smaller thank 2^k * (n')
  by_cases h_1 :  2^k' * n' ≤ 2^k * n
  by_cases h_2 : 2^k * n ≤ 2^k' * (n' + 1)
  right
  left
  intros x h1
  rcases h1 with ⟨h_left, h_right⟩
  constructor
  simp
  sorry
  sorry
  have hp :  2 ^ k * (n+1) ≤ 2 ^ k' * (n' + 1) := by
    sorry
  sorry
  sorry
/-
  ext x
  rw [← Set.setOf_and]
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
  have h0: x< 2 ^ k * n := sorry --lt_of_le_of_lt h4 h_2
  --have c : 2 ^ k * n < 2 ^ k * n := lt_of_le_of_lt h1 h'
  --exact lt_irrefl _ c
  sorry
-/
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

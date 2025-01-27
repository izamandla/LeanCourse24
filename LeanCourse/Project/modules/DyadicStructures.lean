import Mathlib
open Function Set Classical
noncomputable section

/-!
# Dyadic Structures

We define dyadic intervals and dyadic rectangles, along with various lemmas about their properties (disjointness, covering the reals, etc.).
-/

namespace DyadicStructures

/-- Definition 1.1: Dyadic Interval and dyadic rectangle
  A dyadic interval is defined as `[2^k * n, 2^k * (n + 1))`. --/
def dyadicInterval (k n : ℤ) : Set ℝ :=
  { x | (2^k : ℝ) * n ≤ x ∧ x < (2^k : ℝ) * (n + 1) }


/-- Special case: the dyadic interval with `k,n = 0` is `[0, 1)`. --/
@[simp]
theorem zero_dyadicInterval : dyadicInterval 0 0 = Set.Ico 0 1 := by
  ext x
  simp [dyadicInterval]

/-- Special case: the dyadic interval with `k = 0` is `[n, n+1)`. --/
@[simp]
theorem dyadicInterval_of_k_zero (n : ℤ) :
    dyadicInterval 0 n = Set.Ico (n : ℝ) (n+1) := by
  ext x
  simp [Set.Ico, Set.mem_setOf_eq, dyadicInterval, zpow_zero]


/-- Special case: the dyadic interval with `k = 1` is `[2n, 2n+2)`. --/
@[simp]
theorem dyadicInterval_of_k_one (n : ℤ) :
    dyadicInterval 1 n = Set.Ico (2*n : ℝ) (2*n+2) := by
  ext x
  simp [Set.Ico, dyadicInterval]
  intro h
  ring_nf

/-- Special case: the dyadic interval with `k = -1` is `[n/2, (n+1)/2)`. --/
@[simp]
theorem dyadicInterval_of_k_negone (n : ℤ) :
    dyadicInterval (-1) n = Set.Ico (n/2 : ℝ ) ((n + 1)/2) := by
  ext x
  simp [Set.Ico, Set.mem_setOf_eq, dyadicInterval, zpow_neg_one]
  ring_nf

/-- Special case: the dyadic interval with `n = 0` is `[0, 2^k)`. --/
@[simp]
theorem dyadicInterval_of_n_zero (k : ℤ) :
    dyadicInterval k 0 = Set.Ico (0 : ℝ) (2^k : ℝ) := by
  ext x
  simp [dyadicInterval]

/-- Special case: the dyadic interval with `n = 1` is `[2^k, 2^(k+1))`. --/
@[simp]
theorem dyadicInterval_of_n_one (k : ℤ) :
    dyadicInterval k 1 = Set.Ico (2^k : ℝ) (2^(k+1) : ℝ) := by
  ext x
  simp [dyadicInterval]
  intro h
  have h1 : 2 ^ k * (1 + 1) = (2 ^ (k + 1) : ℝ) := by
    calc (2 : ℝ)^k*(1+1)
        = 2*(2 : ℝ)^(k) := by sorry
      _ = (2 ^ (k + 1) : ℝ):= by sorry
  rw [h1]

/--
Points inside the same dyadic interval at scale `k` are within `(2^k : ℝ)` of each other.
-/

theorem dyadicInterval_length (k n : ℤ) (x y : ℝ ) (h : x ∈ dyadicInterval k n ∧ y ∈ dyadicInterval k n) : |x - y| ≤ (2^k : ℝ) := by
  simp [dyadicInterval] at h
  rw[abs_sub_le_iff]
  constructor
  linarith
  linarith

/--
A dyadic interval at scale `k` can be expressed as a union of two smaller intervals of the scale `k - 1`.
-/

theorem scale_up (k n : ℤ) : dyadicInterval k n = { x | (2^(k-1) : ℝ)*(2*n) ≤ x ∧ x < (2^(k-1) : ℝ)*(2*n+2) } := by
  ext x
  simp [dyadicInterval]
  rw[← mul_assoc]
  constructor
  intro h
  constructor
  let h_1 :=h.1
  rw[ ← mul_comm 2]--,mul_self_zpow 2 (k-1)]
  sorry
  sorry
  sorry


/-- A dyadic interval can be split into two smaller dyadic intervals. --/
lemma dyadicInterval_split (k n : ℤ) :
  dyadicInterval k n = dyadicInterval (k - 1) (2 * n) ∪ dyadicInterval (k - 1) (2 * n + 1) := by
  ext x
  simp[dyadicInterval]
  have : 2 = (2 : ℝ)^(1 : ℤ) := by simp
  have h1 : (2 : ℝ ) ^ (k - 1) * 2 = 2 ^ k := by
    calc (2 : ℝ)^(k-1) * 2
        = (2 : ℝ)^(k-1) * (2 : ℝ)^(1 : ℤ) := by simp
      _ = (2 : ℝ)^((k-1) + 1)        := by sorry --rw [ ← zpow_add 2 (k-1) 1]
      _ = 2^k                        := by simp
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


/--
The dyadic intervals at scale `k` cover the entire real line.
-/

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

/--
If `n < n'`, then the dyadic intervals at scale `k` indexed by `n` and `n'` are disjoint.
-/
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

/--
Dyadic intervals at the same scale `k` and different indices `n ≠ n'` are disjoint.
-/
theorem dyadicInterval_disjoint {k n n' : ℤ} (h : n ≠ n') : (dyadicInterval k n ∩ dyadicInterval k n') = ∅ := by
  by_cases h1 : n<n'
  apply dyadicInterval_disjoint_help
  apply h1
  push_neg at h1
  have h1' : n' < n := by
    exact lt_of_le_of_ne h1 (id (Ne.symm h))
  rw[Set.inter_comm]
  apply dyadicInterval_disjoint_help
  apply h1'



theorem dyadic_intervals_relation {k k' n n' : ℤ} (h : k < k') :
  dyadicInterval k n ∩ dyadicInterval k' n' = ∅ ∨
  dyadicInterval k n ⊆ dyadicInterval k' n' ∨
  dyadicInterval k' n' ⊆ dyadicInterval k n := by
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
  push_neg at hn2
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
  sorry
  push_neg at hn1
  left
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
  have h_10 :  (2 ^ k * (↑n+1) : ℝ ) ≤ ↑n' * 2 ^ k' := by
    sorry
  linarith


/-- Theorem: Two dyadic intervals are either disjoint or one is contained in the other. --/
theorem dyadic_intervals_disjoint_or_contained_2ndapproach (k k' n n' : ℤ) :
  (dyadicInterval k n ∩ dyadicInterval k' n' = ∅) ∨
  (dyadicInterval k n ⊆ dyadicInterval k' n') ∨
  (dyadicInterval k' n' ⊆ dyadicInterval k n) := by
  by_cases h : k=k'
  rw[h]
  by_cases hn : n=n'
  rw[hn]
  simp
  push_neg at hn
  left
  apply dyadicInterval_disjoint hn
  push_neg at h
  by_cases h1 : k<k'
  apply dyadic_intervals_relation
  apply h1
  push_neg at h1
  have h_lt : k' < k := lt_of_le_of_ne h1 h.symm
  rw[Set.inter_comm,← or_assoc, or_right_comm, or_assoc]
  apply dyadic_intervals_relation h_lt


/-- A dyadic rectangle is the Cartesian product of two dyadic intervals. --/
def dyadicRectangle (k n k' n' : ℤ) : Set (ℝ × ℝ)  :=
  (dyadicInterval k n).prod (dyadicInterval k' n')

/-- Collection of dyadic intervals at a fixed scale.--/
def SetDyadicIntervals (m : ℕ) : Set (Set ℝ) :=
  {dyadicInterval (-m) n | n ∈ Finset.range (2^m)}

/- Tile-/
def Tile (I : Set ℝ) (ω : Set ℝ) : Prop :=
  ∃ k n : ℤ, I = dyadicInterval k n ∧ ω = {x | x = 2^(-k)}

end DyadicStructures

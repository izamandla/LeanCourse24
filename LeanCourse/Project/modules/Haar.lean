import Mathlib
open Function Set Classical
noncomputable section

/- ## Haar and Rademacher functions -/
namespace Haar

/--
Definition of Haar function `h(x)`.
-/
def haarFunction (x : ℝ) : ℝ :=
  if 0 ≤ x ∧ x < 1/2 then 1
  else if 1/2 ≤  x ∧ x < 1 then -1
  else 0

/--
Left half of haar function is equal to one.
-/
@[simp]
theorem haarFunction_left_half (x : ℝ) (h : 0 ≤ x ∧ x < 1 / 2) : haarFunction x = 1 := by
  unfold haarFunction
  exact if_pos h

/--
Right half of haar function is equal to minus one.
-/
@[simp]
theorem haarFunction_right_half (x : ℝ) (h : 1 / 2 ≤ x ∧ x < 1) : haarFunction x = -1 := by
  unfold haarFunction
  split_ifs with h1
  linarith
  linarith

/--
Haar function is 0 outisde`[0,1)`.
-/
@[simp]
theorem haarFunction_outside (x : ℝ) (h : x < 0 ∨ x ≥ 1) : haarFunction x = 0 := by
  unfold haarFunction
  split_ifs with h1 h2
  have h3 : ¬ (x < 0 ∨ x ≥ 1) := by
    let ⟨hP, hQ⟩ := h1
    push_neg
    constructor
    apply hP
    exact lt_trans hQ (by norm_num)
  contradiction
  have h3 : ¬ (x < 0 ∨ x ≥ 1) := by
    let ⟨hP, hQ⟩ := h2
    push_neg
    constructor
    exact le_trans (by norm_num) hP
    apply hQ
  contradiction
  linarith

@[simp]
theorem haar_sqr (x : ℝ): (haarFunction x)^2 = if 0 ≤ x ∧ x < 1 then 1 else 0 := by
  split_ifs with h
  let ⟨hP, hQ⟩ := h
  by_cases h1 : x< 1/2
  rw[haarFunction_left_half ]
  simp
  constructor
  apply hP
  apply h1
  push_neg at h1
  rw[haarFunction_right_half ]
  simp
  constructor
  apply h1
  apply hQ
  rw[not_and_or] at h
  push_neg at h
  rw[sq_eq_zero_iff]
  apply haarFunction_outside
  apply h

/--
The integral of Haar function over `[0,1)` equals 0.
-/

--@[simp]
theorem haar_integral : ∫ x in Set.Ico 0 1, haarFunction x = 0 := by
  have hs : MeasurableSet (Set.Ico 0 (1/2 : ℝ )) := by
    simp
  have ht : MeasurableSet (Set.Ico (1/2 : ℝ ) 1) := by
    simp
  have h1: MeasureTheory.IntegrableOn haarFunction (Set.Ico 0 (1/2)) := by
    sorry
  have h2: MeasureTheory.IntegrableOn haarFunction (Set.Ico (1/2) 1) := by
    sorry
  have h : Disjoint (Set.Ico (0 : ℝ ) (1/2)) (Set.Ico (1/2) 1) := by
    simp
  have h0 : Set.Ico (0 : ℝ ) 1 = Set.Ico 0 (1/2) ∪ Set.Ico (1/2) 1 := by
    refine Eq.symm (Ico_union_Ico_eq_Ico ?h₁ ?h₂)
    simp
    linarith
  rw[h0]
  rw[MeasureTheory.integral_union h ht h1 h2 ]
  have h_left : EqOn (haarFunction) 1  (Ico 0 (1/2)):= by
    apply haarFunction_left_half
  have h_right: EqOn (haarFunction) (-1)  (Ico (1/2) 1) := by
    apply haarFunction_right_half
  rw[MeasureTheory.setIntegral_congr hs h_left ,MeasureTheory.setIntegral_congr ht h_right]
  simp
  norm_num


/--
The integral of squere of Haar function over `[0,1)` equals 1.
-/
theorem haar_integral_sqr : ∫ x in Set.Ico 0 1, (haarFunction x) ^ 2 = 1 := by
  have h : EqOn (fun x ↦ haarFunction x ^ 2) 1  (Ico 0 1):= by
    intro x hx
    simp_all
  have h1 : MeasurableSet (Set.Ico (0 : ℝ ) 1) := by
    simp
  rw [MeasureTheory.setIntegral_congr h1 h]
  simp


/--
Definition of caled Haar function `h_I(x)` for dyadic interval `I = [2^k n, 2^k (n+1))`.
-/
def haarFunctionScaled (k n : ℤ ) (x : ℝ) : ℝ :=
  2^((-k / 2) : ℝ) * haarFunction (2^(-k) * x - n)


/--
Left half of scaled Haar function is equal to `2^(-k / 2)`.
-/
@[simp]
theorem haarFunctionScaled_left_half (k n : ℤ ) (x : ℝ) (h1 : 0 ≤ 2 ^(-k)  * x - n )(h2: 2 ^ (-k)  * x - n < 1 / 2) :
  haarFunctionScaled k n x = 2 ^ ((-k / 2) : ℝ) := by
  simp[haarFunctionScaled]
  rw [haarFunction_left_half]
  · simp
  · rw[← zpow_neg]
    constructor
    · linarith
    · linarith



/--
Right half of the scaled Haar function is equal to `-2^(-k / 2)`.
-/
@[simp]
theorem haarFunctionScaled_right_half (k n : ℤ ) (x : ℝ) (h1 : 1 / 2 ≤ 2^(-k) * x - n )(h2: 2 ^(- k) * x - n < 1) :
  haarFunctionScaled k n x = -2 ^ (-k / 2 : ℝ) := by
  simp[haarFunctionScaled]
  rw [haarFunction_right_half]
  · simp
  · rw[← zpow_neg]
    constructor
    · linarith
    · linarith

/--
Scaled Haar function is 0 outside `[2^k n, 2^k (n+1))`.
-/
@[simp]
theorem haarFunctionScaled_outside (k n : ℤ ) (x : ℝ)
  (h : 2 ^(- k) * x - n < 0 ∨ 2 ^ (-k) * x - n ≥ 1) :
  haarFunctionScaled k n x = 0 := by
  unfold haarFunctionScaled
  rw [haarFunction_outside _ h]
  simp


/--
Scaled Haar function of positive `k` and `n ∈ {0,...,2^k -1}` is 0 outside `[0,1)`.
-/
@[simp]
theorem haarFunctionScaled_outside_zero_one {k n : ℕ  } {x : ℝ}
  (h : x < 0 ∨ x≥ 1)(hn1 : n ≥ 0)(hn2: n ≤ (2^(-k : ℤ ) -1 : ℝ ))  : haarFunctionScaled k n x = 0 := by
  apply haarFunctionScaled_outside
  rw[zpow_neg ] at hn2
  simp
  obtain h_l|h_r := h
  · left
    have : (2 ^ k)⁻¹* x <0 := by
      rw[mul_comm]
      apply mul_neg_of_neg_of_pos
      · linarith
      · simp
    apply lt_of_lt_of_le this
    linarith
  · right
    have h1 :  (2 ^ k)⁻¹ * (x-1) +1 ≤  (2 ^ k)⁻¹ * x - ↑n := by
      rw[mul_sub]
      simp
      rw[sub_add, sub_le_sub_iff_left (a:=((2 ^ k)⁻¹ * x ))]
      exact hn2
    have h2 : 1 ≤   (2 ^ k)⁻¹ * (x-1) +1 := by
      simp
      linarith
    exact Preorder.le_trans 1 ((2 ^ k)⁻¹ * (x - 1) + 1) ((2 ^ k)⁻¹ * x - ↑n) h2 h1



theorem haarFunctionScaled_mul{k n n' : ℤ } (x :ℝ ) (h_diff : n ≠ n') : haarFunctionScaled k n x  * haarFunctionScaled k n' x = 0 := by
  by_cases h: 2 ^ (-k) * x - n < 0 ∨ 2 ^ (-k) * x - n ≥ 1
  · rw[haarFunctionScaled_outside k n]
    linarith
    exact h
  · rw[not_or] at h
    push_neg at h
    obtain ⟨h_1, h_2⟩ := h
    simp only [zpow_neg] at h_2
    apply lt_add_of_sub_left_lt at h_2
    rw[haarFunctionScaled_outside k n']
    · simp
    · by_cases h1:  n<  n'
      · left
        rw[← Int.add_one_le_iff]at h1
        simp
        apply lt_of_lt_of_le h_2
        norm_cast
      · push_neg at h1
        rw[le_iff_lt_or_eq] at h1
        obtain h_11|h_12 := h1
        · right
          rw[← Int.add_one_le_iff]at h_11
          simp at h_1
          simp
          rw[le_sub_iff_add_le, add_comm ]
          norm_cast
          --exact le_trans h_11 h_1
          sorry
        · left
          exfalso
          rw[eq_comm] at h_12
          exact h_diff h_12

/--
Orthogonality of scaled Haar functions on intervals of the same length.
-/
theorem haarFunctionScaled_orthogonal {k n n' : ℤ } (h_diff : n ≠ n') : ∫ x in Set.Ico 0 1, haarFunctionScaled k n x * haarFunctionScaled k n' x = 0 := by
  simp [haarFunctionScaled_mul _ h_diff]



/--
The square of the scaled Haar function is `2^k` within its support and `0` outside.
-/
@[simp]
theorem haarFunctionScaled_sqr (k n : ℤ ) (x : ℝ) (h1 : 0 ≤ 2 ^ (-k) * x - n) (h2 :2 ^ (-k) * x - n < 1) : (haarFunctionScaled k n x) ^ 2 = 2^(-k):= by
  simp[haarFunctionScaled]
  rw[mul_pow, haar_sqr]
  simp
  have h : (2 ^ (-k / 2:ℝ) : ℝ ) ^ 2 = 2^(-k) := by
    rw [← Real.rpow_mul_natCast]
    · simp
      rw[ ← zpow_neg]
      norm_cast
    · linarith
  split_ifs with h_1
  · obtain ⟨ h_11, h_12⟩ := h_1
    rw[h]
    simp
  · exfalso
    rw[not_and_or] at h_1
    obtain h_11|h_12 := h_1
    · push_neg at h_11
      rw[← zpow_neg] at h_11
      linarith
    · push_neg at h_12
      rw[← zpow_neg] at h_12
      linarith

/--
Product of scaled Haar functions on the same interval.
-/

theorem haarFunction_product0 (k n : ℤ ) (x y : ℝ) (h:  2 ^ (-k) * x - ↑n < 0 ∨ 1≤  2 ^ (-k) * x - ↑n): haarFunctionScaled k n x  * haarFunctionScaled k n y  = 0 := by
  rw[haarFunctionScaled_outside]
  · simp
  · exact h

theorem haarFunction_product0' (k n : ℤ ) (x y : ℝ) (h:  2 ^ (-k) * y - ↑n < 0 ∨ 1≤  2 ^ (-k) * y - ↑n): haarFunctionScaled k n x  * haarFunctionScaled k n y  = 0 := by
  rw[mul_comm]
  apply haarFunction_product0
  exact h

theorem haarFunction_product1 (k n : ℤ ) (x y : ℝ) (h1: 0 ≤ 2 ^ (-k) * x - ↑n)(h2: 2 ^ (-k) * x - ↑n<1/2) (h3: 0 ≤ 2 ^ (-k) * y - ↑n )(h4:2 ^ (-k) * y - ↑n<1/2): haarFunctionScaled k n x  * haarFunctionScaled k n y  = 2^(-k) := by
  rw[haarFunctionScaled_left_half ,haarFunctionScaled_left_half]
  · rw[← pow_two]
    rw [← Real.rpow_mul_natCast]
    · simp
      rw[ ← zpow_neg]
      norm_cast
    · linarith
  · exact h3
  · exact h4
  · exact h1
  · exact h2

theorem haarFunction_product2 (k n : ℤ ) (x y : ℝ) (h1: 1/2≤ 2 ^ (-k) * x - ↑n)(h2: 2 ^ (-k) * x - ↑n<1) (h3: 1/2 ≤ 2 ^ (-k) * y - ↑n )(h4:2 ^ (-k) * y - ↑n<1): haarFunctionScaled k n x  * haarFunctionScaled k n y  = 2^(-k) := by
  rw[haarFunctionScaled_right_half ,haarFunctionScaled_right_half]
  simp
  · rw[← pow_two]
    rw [←Real.rpow_mul_natCast]
    · simp
      rw[ ← zpow_neg]
      norm_cast
    · linarith
  · exact h3
  · exact h4
  · exact h1
  · exact h2


theorem haarFunction_product3 (k n : ℤ ) (x y : ℝ) (h1: 1/2≤ 2 ^ (-k) * x - ↑n)(h2: 2 ^ (-k) * x - ↑n<1) (h3: 0 ≤ 2 ^ (-k) * y - ↑n )(h4:2 ^ (-k) * y - ↑n<1/2): haarFunctionScaled k n x  * haarFunctionScaled k n y  = -2^(-k) := by
  rw[haarFunctionScaled_right_half ,haarFunctionScaled_left_half]
  simp
  · rw[← pow_two]
    rw [←Real.rpow_mul_natCast]
    · simp
      rw[← zpow_neg]
      norm_cast
    · linarith
  · exact h3
  · exact h4
  · exact h1
  · exact h2



/--
The integral of squere of scaled Haar function over `[2^k n, 2^k (n+1))` equals `2^k`.
-/
theorem haarFunctionScaled_normalization (k n : ℤ ) : ∫ x in Set.Ico (2^k*n : ℝ) (2^k*(n+1) : ℝ), (haarFunctionScaled k n x)^2 = 1 := by
  have h : EqOn (fun (x) ↦ haarFunctionScaled k n x ^ 2) (2 ^ (-k))  (Set.Ico (2^k*n : ℝ) (2^k*(n+1) : ℝ)):= by
    intro x hx
    simp
    simp at hx
    obtain ⟨hx1,hx2 ⟩ := hx
    rw[haarFunctionScaled_sqr]
    · simp
    · norm_num
      rw[mul_comm, le_mul_inv_iff₀]
      · linarith
      · apply zpow_pos_of_pos
        simp
    · norm_num
      rw[sub_lt_iff_lt_add', mul_comm, ← lt_mul_inv_iff₀ ]
      · simp
        linarith
      · simp
        apply zpow_pos_of_pos
        simp
  have h1 : MeasurableSet (Set.Ico (2^k*n : ℝ) (2^k*(n+1) : ℝ)) := by
    simp
  rw [MeasureTheory.setIntegral_congr h1 h]
  simp
  have : ((2 ^ k : ℝ ) * (↑n + 1) - 2 ^ k * ↑n) = 2^k := by
    rw[mul_add]
    simp
  rw[this]
  rw[ENNReal.toReal_ofReal]
  · rw[← zpow_neg, ← zpow_add₀]
    simp
    simp
  · apply le_of_lt
    apply zpow_pos_of_pos
    simp



/--
Definition of the Rademacher function `r_n(x)`.
-/
def rademacherFunction (k : ℕ) (t : ℝ) : ℝ :=
  2^(- k / 2 : ℝ ) * ∑ n in Finset.range k, haarFunctionScaled (-(k : ℤ)) n t





@[simp]
theorem rademacherFunction_outside (k : ℕ) (t : ℝ) (h : t < 0 ∨ t ≥ 1) :
  rademacherFunction k t = 0 := by
  unfold rademacherFunction
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro l hl

 /-apply haarFunctionScaled_outside_zero_one
  · exact h
  · simp
  · sorry
  · sorry-/
  sorry

/--
Orthogonality of Rademacher functions.
-/
theorem rademacherFunction_orthogonal (k m : ℕ) : ∫ x in Set.Ico 0 1, rademacherFunction k x * rademacherFunction m x = if k = m then 1 else 0 := by
  sorry


/--
The integral of squere of Rademacher function over `[0,1)` equals 1.
-/
theorem rademacherFunction_normalization (k : ℕ) :
  ∫ x in Set.Icc 0 1, (rademacherFunction k x)^2 = 1 := by
  sorry


end Haar

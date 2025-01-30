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
  2^((k / 2) : ℝ) * haarFunction (2^k * x - n)


/--
Left half of scaled Haar function is equal to `2^(k / 2)`.
-/
@[simp]
theorem haarFunctionScaled_left_half (k n : ℤ ) (x : ℝ) (h : 0 ≤ 2 ^ k  * x - n ∧ 2 ^ k  * x - n < 1 / 2) :
  haarFunctionScaled k n x = 2 ^ ((k / 2) : ℝ) := by
  simp[haarFunctionScaled]
  rw [haarFunction_left_half _ h]
  simp


/--
Right half of the scaled Haar function is equal to `-2^(k / 2)`.
-/
@[simp]
theorem haarFunctionScaled_right_half (k n : ℤ ) (x : ℝ) (h : 1 / 2 ≤ 2 ^ k * x - n ∧ 2 ^ k * x - n < 1) :
  haarFunctionScaled k n x = -2 ^ (k / 2 : ℝ) := by
  unfold haarFunctionScaled
  rw [haarFunction_right_half _ h]
  simp

/--
Scaled Haar function is 0 outside `[2^k n, 2^k (n+1))`.
-/
@[simp]
theorem haarFunctionScaled_outside (k n : ℤ ) (x : ℝ)
  (h : 2 ^ k * x - n < 0 ∨ 2 ^ k * x - n ≥ 1) :
  haarFunctionScaled k n x = 0 := by
  unfold haarFunctionScaled
  rw [haarFunction_outside _ h]
  simp


/--
Scaled Haar function is 0 outside `[2^k n, 2^k (n+1))`.
-/
@[simp]
theorem haarFunctionScaled_outside_zero_one {k n : ℤ } {x : ℝ}
  (h1 : x < 0 ∨ x≥ 1)(hk : k ≤ 0 ) (hn : n ≥ 0)  : haarFunctionScaled k n x = 0 := by
  apply haarFunctionScaled_outside
  simp
  sorry


theorem haarFunctionScaled_mul{k n n' : ℤ } (x :ℝ ) (h_diff : n ≠ n') : haarFunctionScaled k n x  * haarFunctionScaled k n' x = 0 := by
  by_cases h: 2 ^ k * x - n < 0 ∨ 2 ^ k * x - n ≥ 1
  rw[haarFunctionScaled_outside k n]
  linarith
  exact h
  rw[not_or] at h
  push_neg at h
  obtain ⟨h_1, h_2⟩ := h
  /-have h1 : {0 ≤ 2 ^ k * x - ↑n ∧ 2 ^ k * x - ↑n < 1}  {0 ≤ 2 ^ k * x - ↑n' ∧ 2 ^ k * x - ↑n' < 1} = ∅ := by
    simp-/
  rw[haarFunctionScaled_outside k n']
  simp
  by_cases h1:  n≤  n'
  right
  sorry
  left
  push_neg at h1
  sorry


/--
Orthogonality of scaled Haar functions on intervals of the same length.
-/
theorem haarFunctionScaled_orthogonal {k n n' : ℤ } (h_diff : n ≠ n') : ∫ x in Set.Ico 0 1, haarFunctionScaled k n x * haarFunctionScaled k n' x = 0 := by
  simp [haarFunctionScaled_mul _ h_diff]



/--
The square of the scaled Haar function is `2^k` within its support and `0` outside.
-/
@[simp]
theorem haarFunctionScaled_sqr (k n : ℤ ) (x : ℝ) :
  (haarFunctionScaled k n x) ^ 2 = if  0 ≤ 2 ^ k * x - n ∧ 2 ^ k * x - n < 1  then 2 ^ k else 0 := by
  simp[haarFunctionScaled]
  rw[mul_pow, haar_sqr (2 ^ k * x - ↑n)]
  simp
  have : (2 ^ (↑k / 2:ℝ) : ℝ ) ^ 2 = 2^k := by
    rw [← Real.rpow_mul_natCast]
    simp
    linarith
  rw[this]


 /-
  theorem haarFunctionScaled_support (k n : ℕ) (x : ℝ) :
  haarFunctionScaled k n x ≠ 0 ↔ n * 2^k ≤ x ∧ x < (n + 1) * 2^k := by
  unfold haarFunctionScaled
  rw [haarFunction_outside]
  simp-/
/--
Product of scaled Haar functions on the same interval.
-/
theorem haarFunction_product (k n : ℤ ) (x y : ℝ) : haarFunctionScaled k n x  * haarFunctionScaled k n y  =
  if   ((n*2^k ≤ x ∧ x < (n+ 1)*2^k) ∧ (n*2^k ≤ y ∧ y < (n+ 1)*2^k)) then
    if ((n*2^k ≤ x ∧ x < (n+ 1/2)*2^k) ∧ (n*2^k ≤ y ∧ y < (n+ 1/2)*2^k)) then 1
    else if (((n+ 1/2)*2^k ≤ x ∧ x < (n+ 1)*2^k) ∧ ((n+ 1/2)*2^k ≤ y ∧ y < (n+ 1/2)*2^k)) then 1
    else -1
  else 0 := by
  sorry

/--
The integral of squere of scaled Haar function over `[2^k n, 2^k (n+1))` equals `2^k`.
-/
theorem haarFunctionScaled_normalization (k n : ℤ ) : ∫ x in Set.Ico (2^k*n : ℝ) (2^k*(n+1) : ℝ), (haarFunctionScaled k n x)^2 = (2 ^(2*k)) := by
  simp [haarFunctionScaled_sqr]
  have h : EqOn (fun (x) ↦ haarFunctionScaled k n x ^ 2) (2 ^ k)  (Set.Ico (2^k*n : ℝ) (2^k*(n+1) : ℝ)):= by
    intro x hx
    sorry
  have h1 : MeasurableSet (Set.Ico (2^k*n : ℝ) (2^k*(n+1) : ℝ)) := by
    simp
  /-rw [MeasureTheory.setIntegral_congr h1 h]
  simp
  norm_num
  ring-/
  sorry


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
  apply haarFunctionScaled_outside_zero_one
  exact h
  simp
  simp

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

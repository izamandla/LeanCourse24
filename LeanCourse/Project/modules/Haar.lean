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
  simp [haarFunction, h]
  intro h0
  split_ifs with h1
  exfalso
  sorry
  sorry

/--
Right half of haar function is equal to minus one.
-/
@[simp]
theorem haarFunction_right_half (x : ℝ) (h : 1 / 2 ≤ x ∧ x < 1) : haarFunction x = -1 := by
  simp [haarFunction, h]
  sorry

/--
Haar function is 0 outisde`[0,1)`.
-/
@[simp]
theorem haarFunction_outside (x : ℝ) (h : x < 0 ∨ x ≥ 1) : haarFunction x = 0 := by
  simp [haarFunction, h]
  sorry

/--
The integral of Haar function over `[0,1)` equals 0.
-/
@[simp]
theorem haar_integral : ∫ x in Set.Icc 0 1, haarFunction x = 0 := by
  simp [haarFunction]
  sorry

/--
The integral of squere of Haar function over `[0,1)` equals 1.
-/
theorem haar_integral_sqr : ∫ x in Set.Icc 0 1, (haarFunction x)^2 = 1 := by
  simp [haarFunction]
  sorry

/--
Definition of caled Haar function `h_I(x)` for dyadic interval `I = [2^k n, 2^k (n+1))`.
-/
def haarFunctionScaled (k n : ℕ) (x : ℝ) : ℝ :=
  2^(k / 2 : ℝ) * haarFunction (2^k * x - n)


/--
Orthogonality of scaled Haar functions on intervals of the same length.
-/
theorem haarFunctionScaled_orthogonal {k n n' : ℕ} (h_diff : n ≠ n') : ∫ x in Set.Icc 0 1, haarFunctionScaled k n x * haarFunctionScaled k n' x = 0 := by
  simp_rw [haarFunctionScaled, mul_assoc, mul_comm]
  ring_nf
  have h : ∀ x : ℝ,  haarFunction (x * 2 ^ k - ↑n) * haarFunction (x * 2 ^ k - ↑n') = 0 :=by
    sorry
  sorry

/--
Scaled Haar function is 0 outside `[2^k n, 2^k (n+1))`.
-/
theorem haarFunctionScaled_support (k n : ℕ) (x : ℝ) :
  haarFunctionScaled k n x ≠ 0 ↔ n * 2^k ≤ x ∧ x < (n + 1) * 2^k := by
  simp [haarFunctionScaled, haarFunction]
  sorry

/--
Product of scaled Haar functions on the same interval.
-/
theorem haarFunction_product (k n : ℕ) (x y : ℝ) : haarFunctionScaled k n x  * haarFunctionScaled k n y  =
  if   ((n*2^k ≤ x ∧ x < (n+ 1)*2^k) ∧ (n*2^k ≤ y ∧ y < (n+ 1)*2^k)) then
    if ((n*2^k ≤ x ∧ x < (n+ 1/2)*2^k) ∧ (n*2^k ≤ y ∧ y < (n+ 1/2)*2^k)) then 1
    else if (((n+ 1/2)*2^k ≤ x ∧ x < (n+ 1)*2^k) ∧ ((n+ 1/2)*2^k ≤ y ∧ y < (n+ 1/2)*2^k)) then 1
    else -1
  else 0 := by
  sorry

/--
The integral of squere of scaled Haar function over `[2^k n, 2^k (n+1))` equals 1.
-/
theorem haarFunctionScaled_normalization (k n : ℕ) : ∫ x in Set.Icc (2^k*n : ℝ) (2^k*(n+1) : ℝ), (haarFunctionScaled k n x)^2 = 1 := by
  simp_rw [haarFunctionScaled, pow_two, mul_assoc]
  ring_nf
  sorry


/--
Definition of the Rademacher function `r_n(x)`.
-/
def rademacherFunction (k : ℕ) (t : ℝ) : ℝ :=
  2^(- k / 2 : ℝ ) * ∑ n in Finset.range k, haarFunctionScaled k n t

/--
Orthogonality of Rademacher functions.
-/
theorem rademacherFunction_orthogonal (k m : ℕ) : ∫ x in Set.Icc 0 1, rademacherFunction k x * rademacherFunction m x = if k = m then 1 else 0 := by
  sorry


/--
The integral of squere of Rademacher function over `[0,1)` equals 1.
-/
theorem rademacherFunction_normalization (k : ℕ) :
  ∫ x in Set.Icc 0 1, (rademacherFunction k x)^2 = 1 := by
  sorry


end Haar

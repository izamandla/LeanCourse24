import Mathlib
open Function Set Classical
noncomputable section

/- ## Haar and Rademacher functions -/
namespace Haar

/--
Definition 1.6: Haar function `h(x)`.
-/
def haarFunction (x : ℝ) : ℝ :=
  if 0 ≤ x ∧ x < 1/2 then 1
  else if 1/2 ≤  x ∧ x < 1 then -1
  else 0

@[simp]
theorem haarFunction_left_half (x : ℝ) (h : 0 ≤ x ∧ x < 1 / 2) : haarFunction x = 1 := by
  simp [haarFunction, h]
  intro h1
  sorry

@[simp]
theorem haarFunction_right_half (x : ℝ) (h : 1 / 2 ≤ x ∧ x < 1) : haarFunction x = -1 := by
  simp [haarFunction, h]
  sorry

@[simp]
theorem haarFunction_outside_domain (x : ℝ) (h : x < 0 ∨ x ≥ 1) : haarFunction x = 0 := by
  simp [haarFunction, h]
  sorry

theorem haar_integral : ∫ x in Set.Icc 0 1, haarFunction x = 0 := by
  simp [haarFunction]
  -- Prove the integral of `1` on `[0, 1/2]` cancels with `-1` on `[1/2, 1]`.
  sorry

theorem haar_sqr : ∫ x in Set.Icc 0 1, (haarFunction x)^2 = 1 := by
  simp [haarFunction]
  -- Split into subintervals `[0, 1/2]` and `[1/2, 1]` and compute separately.
  sorry
/--
Scaled Haar function `h_I(x)` for dyadic interval `I = [2^k n, 2^k (n+1))`.
-/
def haarFunctionScaled (k n : ℕ) (x : ℝ) : ℝ :=
  2^(k / 2 : ℝ) * haarFunction (2^k * x - n)

@[simp]
theorem haarFunctionScaled_specific (k n : ℕ) (x : ℝ) (h : n * 2 ^ k ≤ x ∧ x < (n + 1) * 2 ^ k) :
  haarFunctionScaled k n x = 2^(k / 2 : ℝ) * haarFunction (2^k * x - n) := by
  simp [haarFunctionScaled, h]

/--
Orthogonality of scaled Haar functions on intervals of the same length.
-/

theorem haarFunctionScaled_orthogonal {k n n' : ℕ} (h_diff : n ≠ n') : ∫ x in Set.Icc 0 1, haarFunctionScaled k n x * haarFunctionScaled k n' x = 0 := by
  simp_rw [haarFunctionScaled, mul_assoc, mul_comm]
  ring_nf
  have h : ∀ x : ℝ,  haarFunction (x * 2 ^ k - ↑n) * haarFunction (x * 2 ^ k - ↑n') = 0 :=by
    sorry
  sorry


theorem haarFunctionScaled_support (k n : ℕ) (x : ℝ) :
  haarFunctionScaled k n x ≠ 0 ↔ n * 2^k ≤ x ∧ x < (n + 1) * 2^k := by
  simp [haarFunctionScaled, haarFunction]
  -- Use the definition to isolate the condition for nonzero values.
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

/-
Self-normalization of Haar functions: ∫ h_I(x)^2 dx = 1.
-/
theorem haarFunctionScaled_normalization (k n : ℕ) : ∫ x in Set.Icc 0 1, (haarFunctionScaled k n x)^2 = 1 := by
  simp_rw [haarFunctionScaled, pow_two, mul_assoc]
  ring_nf
  sorry


/--
Definition 1.7 the Rademacher function `r_n(x)`.
-/
def rademacherFunction (k : ℕ) (t : ℝ) : ℝ :=
  2^(- k / 2 : ℝ ) * ∑ n in Finset.range k, haarFunctionScaled k n t

/--
Orthogonality of Rademacher functions.
-/
theorem rademacherFunction_orthogonal (k m : ℕ) : ∫ x in Set.Icc 0 1, rademacherFunction k x * rademacherFunction m x = if k = m then 1 else 0 := by
  -- Case analysis on k = m or k ≠ m.
  by_cases h : k = m
  · -- Case k = m: Use self-normalization of Haar functions.
    rw [h]
    simp_rw [rademacherFunction]
    /-rw [← Finset.sum_singleton]
    apply haarFunctionScaled_normalization
  · -- Case k ≠ m: Use orthogonality of Haar functions.
    simp_rw [rademacherFunction]
    rw [← Finset.sum_singleton]
    apply haarFunctionScaled_orthogonal
    exact h-/
    sorry
  sorry

theorem rademacherFunction_normalization (k : ℕ) :
  ∫ x in Set.Icc 0 1, (rademacherFunction k x)^2 = 1 := by
  -- Expand `rademacherFunction` and use the self-normalization of `haarFunctionScaled`.
  sorry


end Haar

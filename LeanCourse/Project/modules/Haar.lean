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

/--
Scaled Haar function `h_I(x)` for dyadic interval `I = [2^k n, 2^k (n+1))`.
-/
def haarFunctionScaled (k n : ℕ) (x : ℝ) : ℝ :=
  2^(k / 2 : ℝ) * haarFunction (2^k * x - n)

/--
Definition 1.7 the Rademacher function `r_n(x)`.
-/
def rademacherFunction (n : ℕ) (t : ℝ) : ℝ :=
  2^(- n / 2 : ℝ ) * ∑ k in Finset.range n, haarFunctionScaled n k t
--- changed so it comes from relation to haar functions

end Haar

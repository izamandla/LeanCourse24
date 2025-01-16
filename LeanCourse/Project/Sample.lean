import Mathlib
/-!
## Project Overview
This project aims to make first steps to prove the Walsh analogue of the Carleson-Hunt theorem
using the Linearized Metric Carleson theorem. Those steps include:
1. Defining dyadic intervals, rectangles, and related structures, and showing some coloraries about them.
2. Defining Haar, Walsh and Rademacher functions, as well as the Walsh-Fourier series and looking at the relations between them.
3. Showing the basic result about the Walsh-Fourier.
-/

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
  by_cases hk : k = k' --they have the same length
  rw[hk]
  by_cases hn : n = n' -- they have the same length and the same beginning
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
  --done for k=k'
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
  rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ -- deviding inequalities for different hypothesis
  have h_10 :  (2 ^ k' * (↑n'+1) : ℝ ) ≤ ↑n * 2 ^ k := by
    by_contra h
    rw[not_le] at hn2
    rw[not_le] at h
    rw[← Int.add_one_le_iff] at hk1
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



/- ## Walsh Functions and Walsh-Fourier Series -/
namespace Walsh

/--
Definition 1.4: Walsh Function `W_n(x)`.
-/
def walsh (n : ℕ) : ℝ → ℝ
| x =>
  if n = 0 then 1 -- Base case: W₀(x) = 1
  else if n % 2 = 0 then -- Case for even n (n = 2m)
    let m := n / 2
    if 0≤ x ∧ x < 0.5 then walsh m (2 * x)
    else if 0.5 ≤ x ∧ x < 1 then  walsh m (2 * x - 1)
    else 0
  else -- Case for odd n (n = 2m + 1)
    let m := n / 2
    if 0≤ x ∧ x < 0.5 then walsh m (2 * x)
    else if 0.5 ≤ x ∧ x < 1 then -walsh m (2 * x - 1)
    else 0


--Trivial example: for `n=0`, `Walsh.walsh 0 x = 1` for any `x`
example : Walsh.walsh 0 (0.123) = 1 := by
  simp [walsh]


-- Definition 1.5
/--
Walsh inner product definition.
-/
def walshInnerProduct (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  ∫ x in Set.Icc 0 1, f x * walsh n x

/--
Walsh Fourier partial sum.
-/
def WalshFourierPartialSum (f : ℝ → ℝ) (N : ℕ) : ℝ → ℝ :=
 λ x => ∑ n in Finset.range N, (walshInnerProduct f n) * walsh n x

/--
Walsh Fourier Series.
-/
def walshFourierSeries (f : ℝ → ℝ) : ℝ → ℝ :=
  λ x => tsum (λ N => WalshFourierPartialSum f N x)
--ten tsum jest tutaj chyba bez sensu

/--
Binary representation of a number as a set of indices.
-/
def binaryRepresentationSet (n : ℕ) : Finset ℕ :=
  Finset.filter (λ m => Nat.testBit n m) (Finset.range (n + 1))

/--
Properties of Binary representation set
-/
theorem factaboutbinaryRepresentationSet (N M : ℕ) : binaryRepresentationSet N \ {M} = binaryRepresentationSet (N - 2^M) := by
    sorry


--Those functions should be in L2 not just ℝ → ℝ
end Walsh



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

/- ## Kernel-/
namespace Kernel
def kernel (N : ℕ) (x y : ℝ) : ℝ :=
    1 + ∑ m in Walsh.binaryRepresentationSet N, ∑ n in Finset.range (2^m), (Haar.haarFunctionScaled m n x) * (Haar.haarFunctionScaled m n y)

end Kernel


/--
Relations between Rademacher and Walsh functions.
-/

theorem walshRademacherRelation (n : ℕ) (x : ℝ) :
  Walsh.walsh n x = ∏ m in Walsh.binaryRepresentationSet n , Haar.rademacherFunction m x := by
  sorry

theorem differentwalshRademacherRelation (n : ℕ) (x : ℝ) :
  Walsh.walsh (2^n) x = Haar.rademacherFunction n x := by
  sorry

theorem walshRademacherRelationresult (M N : ℕ) (h : 2^M ≤ N) (x : ℝ) :
  Walsh.walsh N x = Walsh.walsh (2^M) x * ∏ m in Walsh.binaryRepresentationSet (N - (2^M)) , Haar.rademacherFunction m x := by
  simp [walshRademacherRelation]
  have h1: Walsh.binaryRepresentationSet (2 ^ M) ∪ Walsh.binaryRepresentationSet (N - 2 ^ M)= Walsh.binaryRepresentationSet N := by
    rw[← Walsh.factaboutbinaryRepresentationSet]
    unfold Walsh.binaryRepresentationSet
    sorry

  --unfold binaryRepresentationSet
  sorry

/- ## Additional lemmas needed for the main result -/

/--
Lemma 3.1 (part 1).
-/
theorem lemma1_1 (M N : ℕ) (h : 2^M ≤ N ∧ N < 2^(M+1)) (f : ℝ → ℝ) (x : ℝ) :
  Walsh.WalshFourierPartialSum f (2^M) x =
  ∑ k in Finset.range (2^M) , (∫ y in Set.Icc 0 1, f y * Walsh.walsh (2^M) y * (Haar.haarFunctionScaled M k y)  * Walsh.walsh (2^M) x  * (Haar.haarFunctionScaled M k x) ):=
  sorry

/--
Lemma 3.1 (part 2).
-/
theorem lemma1_2 (M N : ℕ) (h : 2^M ≤ N ∧ N < 2^(M+1)) (f : ℝ → ℝ) (x : ℝ) :
  Walsh.WalshFourierPartialSum f (2^M) x =
  ∑ k in Finset.range (2^M),(∫ y in Set.Icc 0 1, f y * Walsh.walsh N y * (Haar.haarFunctionScaled M k y) ) * Walsh.walsh N x * (Haar.haarFunctionScaled M k x) := by
  rw [lemma1_1]
  sorry
  sorry
  sorry
-- te lematy na górze można przepisać tak żeby były spójne z tym późniejszym

/--
Lemma 3.2
-/
theorem lemma2 (M N N' : ℕ) (h1 : 2^M ≤ N ∧ N < 2^(M+1)) (h2 : N' = N - 2^M)
  (f : ℝ → ℝ) (x : ℝ) :
  ∑ i in Finset.range (N + 1) \ Finset.range (2^M), Walsh.walshInnerProduct f i  * Walsh.walsh i x =
  ∑ i in Finset.range (N' + 1), Walsh.walshInnerProduct (Haar.rademacherFunction M * f ) i * (Haar.rademacherFunction M x) *(Walsh.walsh i x) := by
  sorry


/- ## Main result -/

theorem mainresult (N : ℕ) (f : ℝ → ℝ) (x : ℝ) :
  Walsh.WalshFourierPartialSum f N x = (∫ y in Set.Icc 0 1, f y * Walsh.walsh N y * Walsh.walsh N x * Kernel.kernel N x y) := by
  sorry

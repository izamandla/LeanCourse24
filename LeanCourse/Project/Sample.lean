/- It is fine to import all of Mathlib in your project.
This might make the loading time of a file a bit longer. If you want a good chunk of Mathlib, but not everything, you can `import Mathlib.Tactic` and then add more imports as necessary. -/
import Mathlib


/- open namespaces that you use to shorten names and enable notation. -/
open Function Set Classical

/- recommended whenever you define anything new. -/
noncomputable section

/- Now write definitions and theorems. -/

/- The main goal of master thesis is to prove Walsh analogue of the Carleson-Hunt theorem using Linearised Metric Carleson
theorem.
Here the first step would be proven
-/


-- zastanów się kiedy jest lepiej robić struktury a kiedy definicje


-- Definition 1.1: Dyadic Interval and dyadic rectangle
def dyadicInterval (k n : ℤ) : Set ℝ :=
  { x | (2^k : ℝ) * n ≤ x ∧ x < (2^k : ℝ) * (n + 1) }

def dyadicRectangle (k n k' n' : ℤ) : Set (ℝ × ℝ)  :=
  (dyadicInterval k n).prod (dyadicInterval k' n')

def SetDyadicIntervals (m : ℕ) : Set (Set ℝ) :=
  {dyadicInterval (-m) n | n ∈ Finset.range (2^m)}


--theorem that 2 dyadic intervals are disjoint or one is contained in another
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




-- Definition 1.2: Tile
def Tile (I : Set ℝ) (ω : Set ℝ) : Prop :=
  ∃ k n : ℤ, I = dyadicInterval k n ∧ ω = {x | x = 2^(-k)}

-- Definition 1.3: Dyadic Test Function
/-def dyadicTestFunction (N : ℕ) (coeffs : Fin N → ℝ) (intervals : Fin N → Set ℝ) : ℝ → ℝ :=
  λ x => ∑ k , ∑ n ,coeffs k * (dyadicInterval k n).indicator 1 x
problem z sumowaniem po k i n (coś z finite set) -/

#check dyadicInterval
#check dyadicRectangle
#check Tile

-- Definition 1.4: Walsh Function
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


-- Definition 1.5
-- Walsh inner product
def walshInnerProduct (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  ∫ x in Set.Icc 0 1, f x * walsh n x

-- Walsh Fourier partial sum
def WalshFourierPartialSum (f : ℝ → ℝ) (N : ℕ) : ℝ → ℝ :=
 λ x => ∑ n in Finset.range N, (walshInnerProduct f n) * walsh n x

-- Walsh Fourier Series
def walshFourierSeries (f : ℝ → ℝ) : ℝ → ℝ :=
  λ x => tsum (λ N => WalshFourierPartialSum f N x)
--ten tsum jest tutaj chyba bez sensu

--Those functions should be in L2 not just ℝ → ℝ

-- Definition 1.6
-- Haar function h(x)
def haarFunction (x : ℝ) : ℝ :=
  if 0 ≤ x ∧ x < 1/2 then 1
  else if 1/2 ≤  x ∧ x < 1 then -1
  else 0

-- Scaled Haar function h_I(x) for dyadic interval I = [2^k n, 2^k (n+1))
def haarFunctionScaled (k n : ℕ) (x : ℝ) : ℝ :=
  2^(k / 2 : ℝ) * haarFunction (2^k * x - n)

-- Definition 1.7 of the Rademacher function
def rademacherFunction (n : ℕ) (t : ℝ) : ℝ :=
  sorry

-- binary representation
def binaryReoresentationSet (n : ℕ) : Finset ℕ :=
  Finset.filter (λ m => Nat.testBit n m) (Finset.range (n + 1))

-- Theorem 1: Rademacher function in terms of Haar functions
theorem rademacherHaarRelation (n : ℕ) (t : ℝ) :
  rademacherFunction n t = 2^(- n / 2 : ℝ ) * ∑ k in Finset.range n, haarFunctionScaled n k t :=
  sorry
--tak se bo zdefiniowałam SetDyadicIntervals i go nie używam

-- Theorem 2: Walsh function in terms of Rademacher functions

theorem walshRademacherRelation (n : ℕ) (x : ℝ) :
  walsh n x = ∏ m in binaryReoresentationSet n , rademacherFunction m x :=
  sorry

theorem walshRademacherRelationresult (M N : ℕ) (h : 2^M ≤ N) (x : ℝ) :
  walsh N x = walsh M x * ∏ m in binaryReoresentationSet (N - (2^M)) , rademacherFunction m x :=
  sorry


-- Lemma 3.2: Writting the first sum using SetDyadicIntervals
theorem lemma1_1 (M N : ℕ) (h : 2^M ≤ N ∧ N < 2^(M+1)) (f : ℝ → ℝ) (x : ℝ) :
  WalshFourierPartialSum f (2^M) x =
  ∑ k in Finset.range (2^M) , (∫ y in Set.Icc 0 1, f y * walsh (2^M) y * (haarFunctionScaled M k y)  * walsh (2^M) x  * (haarFunctionScaled M k x) ):=
  sorry

theorem lemma1_2 (M N : ℕ) (h : 2^M ≤ N ∧ N < 2^(M+1)) (f : ℝ → ℝ) (x : ℝ) :
  WalshFourierPartialSum f (2^M) x =
  ∑ k in Finset.range (2^M),(∫ y in Set.Icc 0 1, f y * walsh N y * (haarFunctionScaled M k y) ) * walsh N x * (haarFunctionScaled M k x) := by
  rw [lemma1_1]
  sorry
  sorry
  sorry

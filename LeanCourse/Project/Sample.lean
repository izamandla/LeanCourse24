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

#check SetDyadicIntervals

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


-- Lemma 3.2: Writting the first sum using SetDyadicIntervals
theorem walshHaarDecomposition (M N : ℕ) (h : 2^M ≤ N ∧ N < 2^(M+1)) (f : ℝ → ℝ) (x : ℝ) :
  WalshFourierPartialSum f 2^M =
  ∑ k in Finset.range (2^M) , (∫ y in Set.Icc 0 1, f y * walsh (2^M) y * (haarFunctionScaled k y) ) * walsh (2^M) x (haarFunctionScaled k x) :=
  sorry
-- ∑ k in Finset.range (2^M),(∫ y in Set.Icc 0 1, f y * walsh N y * (haarFunctionScaled k y) ) * walsh N x (haarFunctionScaled k x) :=

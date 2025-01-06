/- It is fine to import all of Mathlib in your project.
This might make the loading time of a file a bit longer. If you want a good chunk of Mathlib, but not everything, you can `import Mathlib.Tactic` and then add more imports as necessary. -/
import Mathlib


/- open namespaces that you use to shorten names and enable notation. -/
open Function Set Classical

/- recommended whenever you define anything new. -/
noncomputable section

/- Now write definitions and theorems. -/

-- Definition 1.1: Dyadic Interval and dyadic rectangle
def dyadicInterval (k n : ℤ) : Set ℝ :=
  { x | (2^k : ℝ) * n ≤ x ∧ x < (2^k : ℝ) * (n + 1) }

def dyadicRectangle (k n k' n' : ℤ) : Set (ℝ × ℝ)  :=
  (dyadicInterval k n).prod (dyadicInterval k' n')

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
    if x < 0.5 then walsh m (2 * x) else walsh m (2 * x - 1)
  else -- Case for odd n (n = 2m + 1)
    let m := n / 2
    if x < 0.5 then walsh m (2 * x) else -walsh m (2 * x - 1)
-- zła definicja - zrobione na całej osi rzeczywistej zamiast na [0,1)

-- Definition 1.5: Walsh Fourier Series
def walshInnerProduct (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  ∫ x in Set.Icc 0 1, f x * walsh n x

def walshFourierSeries (f : ℝ → ℝ) (N : ℕ) : ℝ → ℝ :=
  λ x => ∑ n in Finset.range N, (walshInnerProduct f n) * walsh n x

import Mathlib
open Function Set Classical
noncomputable section

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
def walshFourierPartialSum (f : ℝ → ℝ) (N : ℕ) : ℝ → ℝ :=
 λ x => ∑ n in Finset.range N, (walshInnerProduct f n) * walsh n x

/--
Walsh Fourier Series.
-/
def walshFourierSeries (f : ℝ → ℝ) : ℝ → ℝ :=
  λ x => tsum (λ N => walshFourierPartialSum f N x)
--ten tsum jest tutaj chyba bez sensu

/--
Binary representation of a number as a set of indices.
-/
def binaryRepresentationSet (n : ℕ) : Finset ℕ :=
  Finset.filter (λ m => Nat.testBit n m) (Finset.range (Nat.size n + 1))


/--
Properties of Binary representation set
-/

/- Binary representation set of `0` is empty. -/

theorem binaryRepresentationSet_zero : binaryRepresentationSet 0 = ∅ := by
  simp [binaryRepresentationSet, Nat.testBit_zero]

/--
Condition for being in the binary representation set.
-/

theorem mem_binaryRepresentationSet_iff (n m : ℕ) :
  m ∈ binaryRepresentationSet n ↔ (Nat.testBit n m = true) := by
  simp [binaryRepresentationSet, Finset.mem_filter, Finset.mem_range]
  intro h
  apply m.testBit_implies_ge at h
  rw [ge_iff_le, ← m.lt_size] at h
  linarith

/--
Removing an element from the binary representation set.
-/

theorem remove_bit (N M : ℕ) (h : M ∈ binaryRepresentationSet N) : binaryRepresentationSet N \ {M} = binaryRepresentationSet (N - 2^M) := by
  rw [mem_binaryRepresentationSet_iff ] at h
  ext x
  simp
  constructor
  intro h1
  rcases h1 with ⟨hr, hl⟩
  rw [mem_binaryRepresentationSet_iff N x] at hr
  refine (mem_binaryRepresentationSet_iff (N - 2 ^ M) x).mpr ?h.mp.intro.a
  --apply Nat.testBit_implies_ge at hr
  sorry
  /- maybe useful in the future apply Nat.size_le -/
  sorry




--Those functions should be in L2 not just ℝ → ℝ
end Walsh

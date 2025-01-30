import Mathlib
open Function Set Classical
noncomputable section

/- ## Walsh Functions and Walsh-Fourier Series -/
namespace Walsh


 /--
 Definition of Walsh function.
 -/
def walsh (n : ℕ) : ℝ → ℝ
| x =>
  if x <0 ∨  1 ≤  x then 0
  else if x < 0.5 then
    let m := n / 2
    if n = 0 then 1
    else walsh m (2 * x)
  else
    if n = 0 then 1
    else
      let m := n / 2
      if  n % 2 = 0 then walsh m (2 * x - 1)
      else walsh m (2 * x - 1)
    #check walsh.induct

/--
Walsh function is 0 outisde`[0,1)`.
-/
@[simp]
theorem walsh_not_in {n : ℕ} (x : ℝ) (h : x < 0 ∨  1 ≤ x ) : walsh n x = 0 := by
  unfold walsh
  split_ifs with h1 h2
  exact if_pos h
  simp[h]
  simp[h]

/--
Special case: Walsh function for n=0 is 1 on `[0,1)`.
-/
@[simp]
theorem walsh_zero (x : ℝ) (h :0 ≤ x ∧ x <1 ) : walsh 0 x = 1 := by
  simp [walsh, h]


/--
Special case: Walsh function for n=1.
-/
@[simp]
theorem walsh_one (x : ℝ) : walsh 1 x = if 0 ≤ x ∧ x < 1/2 then 1 else if 1/2 ≤ x ∧ x < 1 then -1 else 0:= by
  split_ifs with h1 h2
  sorry
  sorry
  apply walsh_not_in
  rw [not_and_or] at h1
  push_neg at h1
  rw [not_and_or] at h2
  push_neg at h2
  sorry





/--
Walsh functions are nonzero on `[0,1)`
-/
theorem walsh_in (n : ℕ) (x : ℝ) (h : 0 ≤ x ∧ x < 1) : walsh n x ≠ 0 := by
  unfold walsh
  split_ifs with h1 h2
  simp[h]
  simp[h]
  push_neg
  sorry
  simp[h]
  push_neg
  sorry



/--
Walsh function for n being even.
-/
theorem walsh_even {n : ℕ}{x : ℝ} : walsh (2*n) x = (if x < 0.5 then walsh n (2 * x) else walsh n (2 * x - 1)) := by
  sorry

/--
Walsh function for n being odd.
-/
theorem walsh_odd {n : ℕ}{x : ℝ} : walsh (2*n +1 ) x = (if x < 0.5 then walsh n (2 * x) else -walsh n (2 * x - 1)) := by
  sorry

/--
Relation between Walsh funtion of `2n` and `2n+1`.
-/
theorem walsh_even_oddd {n : ℕ}{x : ℝ} : if  0.5 ≤ x ∧ x < 1 then walsh (2*n) x = - walsh (2*n +1) x else walsh (2*n) x = walsh (2*n +1) x:= by
  unfold walsh
  simp
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 h9
  simp
  exfalso
  exact
  sorry
  all_goals sorry



/--
Walsh function is zero outside the interval `[0, 1)`.
-/
@[simp]
theorem walsh_zero_outside_domain (n : ℕ) (x : ℝ) (h : x < 0 ∨ x ≥ 1) : walsh n x = 0 := by
  simp [walsh, h]


/--
Multiplying Wlash functions of fixed `n` and different arguments.
-/
theorem mul_walsh {n : ℕ} (x y : ℝ ): (walsh n x)*(walsh n y ) =  (if (x <0 ∨  1 ≤  x) ∨ (y <0 ∨  1 ≤  y) then 0 else if (x < 0.5 ∧ y < 0.5) ∨ (x ≥  0.5 ∧ y ≥ 0.5) then 1 else -1) := by
  sorry

/--
Multiplying Wlash functions of fixed `n` and same arguments.
-/
theorem sqr_walsh {n : ℕ} (x : ℝ) (h : 0 ≤ x ∧ x < 1) : (walsh n x)*(walsh n x) = 1 := by
  rw[mul_walsh]
  simp
  sorry



/--
Walsh inner product definition.
-/
def walshInnerProduct (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  ∫ x in Set.Icc 0 1, f x * walsh n x

/--
Walsh functions are orthogonal.
-/
theorem walsh_orthogonality (n m : ℕ) (h : n ≠ m) : walshInnerProduct (walsh n) m = 0 := by
  sorry

/--
Walsh functions have norm 1.
-/
theorem walsh_norm (n : ℕ) :
  walshInnerProduct (walsh n) n = 1 := by
  unfold walshInnerProduct
  sorry

/--
Multiplication Walsh inner product by scalar.
-/
theorem walshInnerProduct_smul (c : ℝ) (f : ℝ → ℝ) (n : ℕ) :
  walshInnerProduct (λ x => c * f x) n = c * walshInnerProduct f n := by
  unfold walshInnerProduct
  simp
  sorry

/--
Multiplication Walsh inner product by function.
-/
theorem mul_walshInnerProduct (f g : ℝ → ℝ) (n : ℕ) (x : ℝ ) :
  walshInnerProduct (λ y ↦ g x * f y) n = ∫ y in Set.Icc 0 1, g x * f y * walsh n y := by
  unfold walshInnerProduct
  simp

/--
Walsh inner product of sum of functions.
-/
theorem walshInnerProduct_add (f g : ℝ → ℝ) (n : ℕ) :
  walshInnerProduct (λ x => f x + g x) n = walshInnerProduct f n + walshInnerProduct g n := by
  sorry

/--
Definition of Walsh Fourier partial sum.
-/
def walshFourierPartialSum (f : ℝ → ℝ) (N : ℕ) : ℝ → ℝ :=
 λ x => ∑ n in Finset.range N, (walshInnerProduct f n) * walsh n x

/--
Definition of Walsh Fourier Series.
-/
def walshFourierSeries (f : ℝ → ℝ) : ℝ → ℝ :=
  λ x => tsum (λ N => walshFourierPartialSum f N x)

/--
Binary representation of a number as a set of indices.
-/
def binaryRepresentationSet (n : ℕ) : Finset ℕ :=
  Finset.filter (λ m => Nat.testBit n m) (Finset.range (Nat.size n + 1))



/--
Binary representation set of `0` is empty.
-/

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
  apply (mem_binaryRepresentationSet_iff (N - 2 ^ M) x).mpr ?h.mp.intro.a
  --apply Nat.testBit_implies_ge at hr
  sorry
  /- maybe useful in the future apply Nat.size_le -/
  sorry



end Walsh

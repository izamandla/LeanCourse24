import LeanCourse.Common
import Mathlib.Data.Complex.Exponential
noncomputable section
open Real Function Nat BigOperators Set Finset
open Classical


/-

* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapters 5 (mostly section 2) and 6 (mostly sections 1 and 2).

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises under "Exercises to hand-in". Deadline: 12.11.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/


/-! # Exercises to practice. -/

/- A note on definitions -/

lemma my_lemma : 3 + 1 = 4 := rfl
def myThree : ℕ := 3

/-
Tactics like `simp` and `rw` will not unfold definitions unless instructed to.
Tactics like `exact` and `apply` will unfold definitions if needed.
Uncomment the following lines one-by-one to see the difference. -/

example : myThree + 1 = 4 := by
  -- rw [my_lemma] -- fails
  -- simp [my_lemma] -- fails to use `my_lemma`
  -- exact my_lemma -- works
  -- apply my_lemma -- works
  -- rw [myThree, my_lemma] -- works after instructing `rw` to unfold the definition
  -- simp [myThree] -- works after instructing `simp` to unfold the definition
                    -- (it doesn't need `my_lemma` to then prove the goal)
  sorry


/- The following exercises are to practice with casts. -/
example (n : ℤ) (h : (n : ℚ) = 3) : 3 = n := by {
  sorry
  }

example (n m : ℕ) (h : (n : ℚ) + 3 ≤ 2 * m) : (n : ℝ) + 1 < 2 * m := by {
  sorry
  }

example (n m : ℕ) (h : (n : ℚ) = m ^ 2 - 2 * m) : (n : ℝ) + 1 = (m - 1) ^ 2 := by {
  sorry
  }

example (n m : ℕ) : (n : ℝ) < (m : ℝ) ↔ n < m := by {
  sorry
  }

example (n m : ℕ) (hn : 2 ∣ n) (h : n / 2 = m) : (n : ℚ) / 2 = m := by {
  sorry
  }

example (q q' : ℚ) (h : q ≤ q') : exp q ≤ exp q' := by {
  sorry
  }

example (n : ℤ) (h : 0 < n) : 0 < Real.sqrt n := by {
  sorry
  }

/- Working with `Finset` is very similar to working with `Set`.
However, some notation, such as `f '' s` or `𝒫 s` doesn't exist for `Finset`. -/
example (s t : Finset ℕ) : (s ∪ t) ∩ t = (s ∩ t) ∪ t := by {
  sorry
  }

example {α β : Type*} (f : α → β) (s : Finset α) (y : β) : y ∈ s.image f ↔ ∃ x ∈ s, f x = y := by {
  sorry
  }

/- `Disjoint` can be used to state that two (fin)sets are disjoint.
Use `Finset.disjoint_left` (or `Set.disjoint_left`) to unfold its definition.
If you have `x ∈ t \ s` apply `simp` first to get a conjunction of two conditions.
-/
example {α : Type*} (s t : Finset α) : Disjoint s (t \ s) := by {
  sorry
  }


/- Let's define the Fibonacci sequence -/
def fibonacci : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | (n + 2) => fibonacci (n + 1) + fibonacci n

/- Prove the following exercises by induction. -/

example (n : ℕ) : ∑ i in range n, fibonacci (2 * i + 1) = fibonacci (2 * n) := by {
  sorry
  }

example (n : ℕ) : ∑ i in range n, (fibonacci i : ℤ) = fibonacci (n + 1) - 1 := by {
  sorry
  }

example (n : ℕ) : 6 * ∑ i in range (n + 1), i ^ 2 = n * (n + 1) * (2 * n + 1) := by {
  sorry
  }

def fac : ℕ → ℕ
  | 0       => 1
  | (n + 1) => (n + 1) * fac n

theorem pow_two_le_fac (n : ℕ) : 2 ^ n ≤ fac (n + 1) := by {
  sorry
  }

example (n : ℕ) : fac n = ∏ i in range n, (i + 1) := by {
  sorry
  }

example (n : ℕ) : fac (2 * n) = fac n * 2 ^ n * ∏ i in range n, (2 * i + 1) := by {
  sorry
  }





/- **Exercise**.
Define scalar multiplication of a real number and a `Point`. -/

@[ext] structure Point where
  x : ℝ
  y : ℝ
  z : ℝ

-- give definition here


/- **Exercise**.Define Pythagorean triples, i.e. triples `a b c : ℕ` with `a^2 + b^2 = c^2`.
Give an example of a Pythagorean triple, and show that multiplying a Pythagorean triple by a
constant gives another Pythagorean triple. -/

-- give definition here



/- Prove that triples of equivalent types are equivalent. -/

@[ext] structure Triple (α : Type*) where
  x : α
  y : α
  z : α

example (α β : Type*) (e : α ≃ β) : Triple α ≃ Triple β := sorry



/- 5. Show that if `G` is an abelian group then triples from elements of `G` is an abelian group. -/

class AbelianGroup' (G : Type*) where
  add (x : G) (y : G) : G
  comm (x y : G) : add x y = add y x
  assoc (x y z : G) : add (add x y) z = add x (add y z)
  zero : G
  add_zero : ∀ x : G, add x zero = x
  neg : G → G
  add_neg : ∀ x : G, add x (neg x) = zero

example (G : Type*) [AbelianGroup' G] : AbelianGroup' (Triple G) := sorry



/-! # Exercises to hand-in. -/

/- **Exercise**.
Define the structure of "strict bipointed types", i.e. a type together with 2 unequal points
`x₀ ≠ x₁` in it.
Then state and prove the lemma that for any element of a strict bipointed type we have
`∀ z, z ≠ x₀ ∨ z ≠ x₁.` -/

-- give the definition here
structure strict_bipointed_types where
  x₀ : Point
  x₁ : Point
  unequal : x₀ ≠ x₁

-- state and prove the lemma here
lemma either_unequal {bp: strict_bipointed_types} (x₀ x₁ : Point): ∀ z, z ≠ bp.x₀ ∨ z ≠ bp.x₁ := by
  intro z
  by_contra hz
  push_neg at hz
  have hx := strict_bipointed_types.unequal bp
  have: bp.x₀ = bp.x₁ := by apply (Eq.congr_left hz.1).mp hz.2
  contradiction


/- Prove by induction that `∑_{i = 0}^{n} i^3 = (∑_{i=0}^{n} i) ^ 2`. -/
open Finset in

lemma sum_square_eq_sq_sum (n : ℕ) : ∑ i in range (n + 1), (i : ℚ) = n * (n + 1) / 2 := by {
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    field_simp
    ring
  }

lemma sum_cube_eq_sq_sum (n : ℕ) :
    (∑ i in range (n + 1), (i : ℚ) ^ 3) = (∑ i in range (n + 1), (i : ℚ)) ^ 2 := by {
    induction n with
    | zero =>
      simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      rw [Finset.sum_range_succ]
      rw [Finset.sum_range_succ]
      rw [← Finset.sum_range_succ]
      rw [add_sq]
      rw [add_assoc]
      rw [add_left_cancel_iff]
      push_cast
      have : (n + 1 : ℚ) ^ 3 = n ^ 3 + 3 * n ^ 2 + 3 * n + 1 := by ring
      rw [this]
      have : (n + 1 : ℚ) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
      rw [this]
      rw [sum_square_eq_sq_sum]
      ring
  }

/-
Suppose `(A i)_i` is a sequence of sets indexed by a well-ordered type
(this is an order where every nonempty set has a minimum element).
We now define a new sequence by `C n = A n \ (⋃ i < n, A i)`.
In this exercise, we show that the new sequence is pairwise disjoint but has the same union as the
original sequence.
-/
lemma disjoint_unions {ι α : Type*} [LinearOrder ι] [wf : WellFoundedLT ι] (A C : ι → Set α)
  (hC : ∀ i, C i = A i \ ⋃ j < i, A j) : Pairwise (Disjoint on C) ∧ ⋃ i, C i = ⋃ i, A i := by {
  have h := wf.wf.has_min  -- this hypothesis allows you to use well-orderedness
  push_neg at h
  constructor
  · intro m n hmn
    by_cases hmn' : n > m
    refine Set.disjoint_right.mpr ?left.a
    intro x hx
    rw [hC n] at hx
    rw [hC m]
    simp at hx
    have := hx.2 m hmn'
    by_contra h'
    simp at h'
    have := h'.1
    contradiction
    push_neg at hmn'
    have hmn: n ≠ m := by apply ne_comm.mp hmn
    have hmn'': n < m := by apply lt_iff_le_and_ne.mpr ⟨hmn', hmn⟩
    refine Set.disjoint_left.mpr ?right.a
    intro x hx
    rw [hC m] at hx
    rw [hC n]
    simp at hx
    have := hx.2 n hmn''
    by_contra h'
    simp at h'
    have := h'.1
    contradiction
  · apply subset_antisymm
    dsimp; gcongr with i
    refine diff_eq_empty.mp ?right.a.h.a
    rw [hC i, diff_diff_comm, diff_self, empty_diff]
    dsimp; gcongr with i
    rw [@Set.subset_def]
    intro x hx
    rw [hC i]
    simp
    constructor
    · exact hx
    intro j hj
    sorry
  }



/- Next, we'll prove that if `2 ^ n - 1` is prime, then `n` is prime.
The first exercise is a preparation, and I've given you a skeleton of the proof for the
second exercise. Note how we do some computations in the integers, since the subtraction on `ℕ`
is less well-behaved.
(The converse is not true, because `89 ∣ 2 ^ 11 - 1`) -/

#check Nat.prime_def_lt

lemma exists_dvd_of_not_prime' {n : ℕ} (h2 : 2 ≤ n) (hnp : ¬ Nat.Prime n) :
  ∃ m, 2 ≤ m ∧ m ≤ n / 2 ∧ m ∣ n := by
  have n_not_prime := hnp
  rw [Nat.prime_def_lt] at hnp
  push_neg at hnp
  have hnp' := hnp h2
  rcases hnp' with ⟨m, m_lt_n, m_dvd_n, m_neq_1⟩
  use m
  constructor
  · refine (two_le_iff m).mpr ?h.left.a
    constructor
    · refine Nat.ne_zero_iff_zero_lt.mpr ?h.left.a.left.a
      by_contra h
      push_neg at h
      by_cases hm0 : m = 0
      rw [hm0] at m_dvd_n
      apply zero_dvd_iff.mp at m_dvd_n
      rw [m_dvd_n] at h2
      contradiction
      by_cases hmneg : m < 0
      have: 0 < m := by linarith
      contradiction
      push_neg at hmneg hm0
      have: m = 0 := by linarith
      contradiction
    · exact m_neq_1
  · constructor
    · by_cases n_eq_2 : n = 2
      rw [n_eq_2] at n_not_prime
      contradiction
      by_cases n_eq_3 : n = 3
      rw [n_eq_3] at n_not_prime
      contradiction
      have n_ge_3 : 3 ≤ n := by sorry
      push_neg at n_eq_3
      have n_gt_3 : 3 < n := by exact Nat.lt_of_le_of_ne n_ge_3 (id (Ne.symm n_eq_3))
      apply dvd_def.mp at m_dvd_n
      rcases m_dvd_n with ⟨c, hc⟩
      rw [hc]
      by_cases hm0 : m = 0
      rw [hm0]
      norm_num
      push_neg at hm0
      have hmpos : 0 < m := zero_lt_of_ne_zero hm0
      have hm_gt_2 : 2 ≤ m := by exact (two_le_iff m).mpr ⟨hm0, m_neq_1⟩
      have c_nonneg: 0 ≤ c:= by linarith
      have n_ge_4 : 4 ≤ n := by linarith
      have c_ge_2 : 2 ≤ c := sorry
      sorry
    · exact m_dvd_n


lemma not_prime_iff (n : ℕ) :
    ¬ Nat.Prime n ↔ n = 0 ∨ n = 1 ∨ ∃ a b : ℕ, 2 ≤ a ∧ 2 ≤ b ∧ n = a * b := by {
    constructor
    intro n_not_prime
    · by_cases hn0 : n = 0
      left; exact hn0
      by_cases hn1 : n = 1
      right; left; exact hn1
      right; right
      -- n ≥ 2
      have hn_ge2 : n ≥ 2 := by
        by_contra hn_lt2
        have hn_lt2' : n < 2 := lt_of_not_ge hn_lt2
        interval_cases n
        contradiction
        contradiction
      have h'' : minFac n < n := by
        apply (not_prime_iff_minFac_lt hn_ge2).mp
        exact n_not_prime
      have := exists_dvd_of_not_prime' hn_ge2 n_not_prime
      rcases this with ⟨m, hm2, hm3, hm4⟩
      use m
      use n / m
      constructor
      · exact hm2
      · constructor
        have: 0 < 2 := by norm_num
        have: 2 ≤ n / m := by
          refine (Nat.le_div_iff_mul_le ?k0).mpr ?_
          linarith [hm2]
          rw [Nat.two_mul]
          have h''': m + m ≤ n / 2 + n / 2 := by apply Nat.add_le_add hm3 hm3
          have: n = n / 2 + n / 2 := by
            ring
            have: Even n := sorry
            rw [div_two_mul_two_of_even]
            exact this
          rw [this]
          exact h'''
        exact this
        exact Eq.symm (Nat.mul_div_cancel' hm4)
    intro h
    rcases h with (rfl | rfl | ⟨a, b, ha, hb, hn⟩)
    · exact Nat.not_prime_zero
    · exact Nat.not_prime_one
    · have ha1 : a ≠ 1 := by linarith
      have hb1 : b ≠ 1 := by linarith
      have := Nat.not_prime_mul ha1 hb1
      rw [← hn] at this
      exact this

  }

lemma prime_of_prime_two_pow_sub_one (n : ℕ) (hn : Nat.Prime (2 ^ n - 1)) : Nat.Prime n := by {
  by_contra h2n
  rw [not_prime_iff] at h2n
  obtain rfl|rfl|⟨a, b, ha, hb, rfl⟩ := h2n
  · simp at hn
    contradiction
  · simp at hn
    contradiction
  have h : (2 : ℤ) ^ a - 1 ∣ (2 : ℤ) ^ (a * b) - 1
  · rw [← Int.modEq_zero_iff_dvd]
    calc (2 : ℤ) ^ (a * b) - 1
        ≡ ((2 : ℤ) ^ a) ^ b - 1 [ZMOD (2 : ℤ) ^ a - 1] := by rw [pow_mul 2 a b]
      _ ≡ (1 : ℤ) ^ b - 1 [ZMOD (2 : ℤ) ^ a - 1] := by
        have : (2 : ℤ) ^ a ≡ 1 [ZMOD (2 : ℤ) ^ a - 1] := by exact Int.modEq_sub (2 ^ a) 1
        refine Int.ModEq.sub ?h₁ rfl
        exact Int.ModEq.pow b this
      _ ≡ 0 [ZMOD (2 : ℤ) ^ a - 1] := by simp
  have h2 : 2 ^ 2 ≤ 2 ^ a := by exact pow_le_pow_of_le_right (by norm_num) ha
  have h3 : 1 ≤ 2 ^ a := by exact Nat.one_le_two_pow
  have h4 : 2 ^ a - 1 ≠ 1 := by zify; simp [h3]; linarith
  have h5 : 2 ^ a - 1 < 2 ^ (a * b) - 1 := by
    apply tsub_lt_tsub_right_of_le h3
    refine (Nat.pow_lt_pow_iff_right ?h'').mpr ?_
    linarith
    refine (Nat.lt_mul_iff_one_lt_right ?ha).mpr hb
    linarith
  have h6' : 2 ^ 0 ≤ 2 ^ (a * b) := by
    refine pow_le_pow_of_le_right ?hx ?_
    linarith
    norm_num
  have h6 : 1 ≤ 2 ^ (a * b) := h6'
  have h' : 2 ^ a - 1 ∣ 2 ^ (a * b) - 1 := by norm_cast at h
  rw [Nat.prime_def_lt] at hn
  have hne_one : 2 ^ a - 1 ≠ 1 := h4
  have hlt : 2 ^ a - 1 < 2 ^ (a * b) - 1 := h5
  have hne_self : 2 ^ a - 1 ≠ 2 ^ (a * b) - 1 := Nat.ne_of_lt hlt
  have hprime := hn.2 (2 ^ a - 1) h5 h'
  contradiction
  }

/- Prove that for positive `a` and `b`, `a^2 + b` and `b^2 + a` cannot both be squares.
Prove it on paper first! -/

lemma not_isSquare_sq_add_or (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ¬ IsSquare (a ^ 2 + b) ∨ ¬ IsSquare (b ^ 2 + a) := by {
      rw[IsSquare, IsSquare]
      by_contra heq
      push_neg at heq
      let r := (a + b^2)
      let r' := b + a^2
      rcases le_or_lt a b with hab | hba
      · apply LE.le.lt_or_eq at hab
        rcases hab with h1 | h2
        · have h : a + b^2 < (b+1)^2 := by
            calc a + b^2 < b + b ^ 2:= by exact Nat.add_lt_add_right h1 (b ^ 2)
              _<(b+1)^2 := by
                ring
                simp
                linarith
      --apply Nat.not_exists_sq



  }

/-- Let's prove that the positive reals form a group under multiplication.
Note: in this exercise `rw` and `simp` will not be that helpful, since the definition is hidden
behind notation. But you can use apply to use the lemmas about real numbers. -/

abbrev PosReal : Type := {x : ℝ // 0 < x}

def groupPosReal : Group PosReal :=
  mul λ a b ⟨a.val * b.val, mul_pos a.property b.property⟩
  mul_assoc := λ a b c, subtype.eq (mul_assoc a.val b.val c.val)
  one := ⟨1, by norm_num⟩
  one_mul := λ a, subtype.eq (one_mul a.val), -- One is the left identity
  mul_one := λ a, subtype.eq (mul_one a.val), -- One is the right identity
  inv := λ a, ⟨a.val⁻¹, inv_pos.2 a.property⟩, -- Inverse of a positive real is also positive
  mul_left_inv := λ a, subtype.eq (mul_inv_cancel (ne_of_gt a.property))
}




/-
Compute by induction the cardinality of the powerset of a finite set.

Hints:
* Use `Finset.induction` as the induction principle, using the following pattern:
```
  induction s using Finset.induction with
  | empty => sorry
  | @insert x s hxs ih => sorry
```
* You will need various lemmas about the powerset, search them using Loogle.
  The following queries will be useful for the search:
  `Finset.powerset, insert _ _`
  `Finset.card, Finset.image`
  `Finset.card, insert _ _`
* As part of the proof, you will need to prove an injectivity condition
  and a disjointness condition.
  Separate these out as separate lemmas or state them using `have` to break up the proof.
* Mathlib already has `card_powerset` as a simp-lemma, so we remove it from the simp-set,
  so that you don't actually simplify with that lemma.
-/
attribute [-simp] card_powerset
#check Finset.induction

lemma fintype_card_powerset (α : Type*) (s : Finset α) :
    Finset.card (powerset s) = 2 ^ Finset.card s := by {
  sorry
  }

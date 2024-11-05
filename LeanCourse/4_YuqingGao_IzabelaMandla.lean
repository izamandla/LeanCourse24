import LeanCourse.Common
import Mathlib.Data.Complex.Exponential
noncomputable section
open Real Function Set Nat
open Classical


/-

* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapter 4, sections 2, 3.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises below. Deadline: 5.11.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/


/-! # Exercises to practice. -/

/- Do the exercises about sets from last exercise set, if you haven't done them because
we didn't cover the material in class yet. -/


variable {α β γ ι : Type*} (f : α → β) (x : α) (s : Set α)

/- Prove this equivalence for sets. -/
example : s = univ ↔ ∀ x : α, x ∈ s := by {
  constructor
  · intro h
    rw [h]
    exact Set.mem_univ
  · intro h
    exact Set.eq_univ_of_forall h
  }


/- Prove the law of excluded middle without using `by_cases`/`tauto` or lemmas from the library.
You will need to use `by_contra` in the proof. -/
lemma exercise3_1 (p : Prop) : p ∨ ¬ p := by {
  by_contra h
  push_neg at h
  exact h.1 h.2
  }

/- `α × β` is the cartesian product of the types `α` and `β`.
Elements of the cartesian product are denoted `(a, b)`, and the projections are `.1` and `.2`.
As an example, here are two ways to state when two elements of the cartesian product are equal.
You can use the `ext` tactic to show that two pairs are equal.
`simp` can simplify `(a, b).1` to `a`.
This is true by definition, so calling `assumption` below also works directly. -/

example (a a' : α) (b b' : β) : (a, b) = (a', b') ↔ a = a' ∧ b = b' := Prod.ext_iff
example (x y : α × β) : x = y ↔ x.1 = y.1 ∧ x.2 = y.2 := Prod.ext_iff
example (a a' : α) (b b' : β) (ha : a = a') (hb : b = b') : (a, b) = (a', b') := by
  ext
  · simp
    assumption
  · assumption

/- To practice, show the equality of the following pair. What is the type of these pairs? -/
example (x y : ℝ) : (123 + 32 * 3, (x + y) ^ 2) = (219, x ^ 2 + 2 * x * y + y ^ 2) := by {
  ext
  · simp
  · ring
  }

/- `A ≃ B` means that there is a bijection from `A` to `B`.
So in this exercise you are asked to prove that there is a bijective correspondence between
  functions from `ℤ × ℕ` to `ℤ × ℤ`
and
  functions from `ℕ` to `ℕ`
This is an exercise about finding lemmas from the library.
Your proof is supposed to only combine results from the library,
you are not supposed to define the bijection yourself.
If you want, you can use `calc` blocks with `≃`. -/
example : (ℤ × ℕ → ℤ × ℤ) ≃ (ℕ → ℕ) := by {
  sorry
  }

/- Prove a version of the axiom of choice Lean's `Classical.choose`. -/
example (C : ι → Set α) (hC : ∀ i, ∃ x, x ∈ C i) : ∃ f : ι → α, ∀ i, f i ∈ C i := by {
  choose f hf using hC
  exact ⟨f, hf⟩
  }


/-! # Exercises to hand-in. -/


/- ## Converging sequences

Prove two more lemmas about converging sequences. -/

/-- From the lecture, the sequence `u` of real numbers converges to `l`. -/
def SequentialLimit (u : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε

/- Let's prove that reindexing a convergent sequence
by a reindexing function that tends to infinity
produces a sequence that converges to the same value. -/
lemma sequentialLimit_reindex {s : ℕ → ℝ} {r : ℕ → ℕ} {a : ℝ}
    (hs : SequentialLimit s a) (hr : ∀ m : ℕ, ∃ N : ℕ, ∀ n ≥ N, r n ≥ m) :
    SequentialLimit (s ∘ r) a := by {
    rw [SequentialLimit] at *
    intros ε hε
    rcases hs ε hε with ⟨N, hN⟩
    rcases hr N with ⟨N', hN'⟩
    use N'
    intros n hn
    specialize hN (r n) (hN' n hn)
    exact hN
  }


/- Let's prove the squeeze theorem for sequences.
You will want to use the lemma in the library that states
`|a| < b ↔ -b < a ∧ a < b`. -/
lemma sequentialLimit_squeeze {s₁ s₂ s₃ : ℕ → ℝ} {a : ℝ}
    (hs₁ : SequentialLimit s₁ a) (hs₃ : SequentialLimit s₃ a)
    (hs₁s₂ : ∀ n, s₁ n ≤ s₂ n) (hs₂s₃ : ∀ n, s₂ n ≤ s₃ n) :
    SequentialLimit s₂ a := by {
    rw [SequentialLimit] at *
    intros ε hε
    rcases hs₁ ε hε with ⟨N₁, hN₁⟩
    rcases hs₃ ε hε with ⟨N₃, hN₃⟩
    use max N₁ N₃
    intros n hn
    apply abs_lt.mpr
    have: n ≥ N₁ := le_of_max_le_left hn
    have h1: -ε < s₁ n - a := (abs_lt.mp (hN₁ n this)).1
    have: n ≥ N₃ := le_of_max_le_right hn
    have h3: s₃ n - a < ε := (abs_lt.mp (hN₃ n this)).2
    constructor
    · linarith [hs₁s₂ n]
    · linarith [hs₂s₃ n]
  }

/- ## Sets -/

/- Prove this without using lemmas from Mathlib. -/
lemma image_and_intersection {α β : Type*} (f : α → β) (s : Set α) (t : Set β) :
    f '' s ∩ t = f '' (s ∩ f ⁻¹' t) := by {
    ext y
    constructor
    · intro h
      rcases h with ⟨⟨x, hx, rfl⟩, hy⟩
      exact ⟨x, ⟨hx, hy⟩, rfl⟩
    · intro h
      rcases h with ⟨x, ⟨hx, hy⟩, rfl⟩
      exact ⟨⟨x, hx, rfl⟩, hy⟩
  }

/- Prove this by finding relevant lemmas in Mathlib. -/
lemma preimage_square :
    (fun x : ℝ ↦ x ^ 2) ⁻¹' {y | y ≥ 16} = { x : ℝ | x ≤ -4 } ∪ { x : ℝ | x ≥ 4 } := by {
    have: √ 16 = 4 := by
      apply (sqrt_eq_iff_mul_self_eq_of_pos _).mpr; linarith; norm_num
    ext x
    field_simp
    constructor
    · intro h
      by_cases hx: x ≥ 0
      right
      calc x
          = √ (x ^ 2) := by rw [sqrt_sq hx]
        _ ≥ √ 16 := by apply sqrt_le_sqrt h
        _ = 4 := this
      left
      push_neg at hx
      calc x
          = -|x| := by linarith [abs_of_neg hx]
        _ = -√ (|x| ^ 2) := by rw [sqrt_sq (abs_nonneg x)]
        _ = -√ (x ^ 2) := by simp
        _ ≤ -√ 16 := by apply neg_le_neg; apply sqrt_le_sqrt h
        _ = -4 := by linarith [this]
    · intro h
      have h1: |x| ≥ 4 := by apply le_abs'.mpr; exact h
      have h2: -|x| ≤ 4 := by linarith
      calc 16
          = 4 ^ 2 := by norm_num
        _ ≤ |x| ^ 2 := by apply sq_le_sq' h2 h1
        _ = √ (|x| ^ 2) ^ 2 := by field_simp
        _ = √ (x ^ 2) ^ 2 := by simp
        _ = x ^ 2 := by field_simp
  }


/- `InjOn` states that a function is injective when restricted to `s`.
`LeftInvOn g f s` states that `g` is a left-inverse of `f` when restricted to `s`.
Now prove the following example, mimicking the proof from the lecture.
If you want, you can define `g` separately first.
-/
lemma inverse_on_a_set [Inhabited α] (hf : InjOn f s) : ∃ g : β → α, LeftInvOn g f s := by {
  let g : β → α := fun y => if h : ∃ x ∈ s, f x = y then Classical.choose h else default
  use g
  intros x hx
  have hfx : ∃ x' ∈ s, f x' = f x := ⟨x, hx, rfl⟩
  have := (Classical.choose_spec hfx).2
  have: f x = f (Classical.choose hfx) := by rw [this]
  rw [hf hx (Classical.choose_spec hfx).1 this]
  sorry
  }


/- Let's prove that if `f : α → γ` and `g : β → γ` are injective function whose
ranges partition `γ`, then `Set α × Set β` is in bijective correspondence to `Set γ`.

To help you along the way, some potentially useful ways to reformulate the hypothesis are given. -/

-- This lemma might be useful.
#check Injective.eq_iff

lemma set_bijection_of_partition {f : α → γ} {g : β → γ} (hf : Injective f) (hg : Injective g)
    (h1 : range f ∩ range g = ∅) (h2 : range f ∪ range g = univ) :
    ∃ (L : Set α × Set β → Set γ) (R : Set γ → Set α × Set β), L ∘ R = id ∧ R ∘ L = id := by {
  -- h1' and h1'' might be useful later as arguments of `simp` to simplify your goal.
  have h1' : ∀ x y, f x ≠ g y := by
    intro x y h
    have heq : g y = f x := by rw [h]
    have : f x ∈ range f ∩ range g := ⟨⟨x, rfl⟩, ⟨y, heq⟩⟩
    rw [h1] at this
    exact Set.not_mem_empty (f x) this
  have h1'' : ∀ y x, g y ≠ f x := by
    intro y x
    exact (h1' x y).symm
  have h2' : ∀ x, x ∈ range f ∪ range g := by
    intro x
    rw [h2]
    exact Set.mem_univ x
  let L : Set α × Set β → Set γ := fun p => f '' p.1 ∪ g '' p.2
  let R : Set γ → Set α × Set β := fun C => (f ⁻¹' C, g ⁻¹' C)
  have L_R : ∀ C : Set γ, L (R C) = C := by
    intro C
    simp only [L, R]
    ext
    constructor
    · intro h
      rcases h with ⟨a, ha1, ha2⟩ | ⟨b, hb1, hb2⟩
      exact ha2 ▸ ha1
      exact hb2 ▸ hb1
    · intro h
      sorry

  have R_L : ∀ p : Set α × Set β, R (L p) = p := by
    intro p
    cases p
    simp only [L, R]
    ext
    constructor
    · intro h
      obtain h | h := h
      · obtain ⟨a, ha, hfa⟩ := h
        exact hf hfa ▸ ha
      · obtain ⟨b, hb, hgb⟩ := h
        sorry
    · intro h
      sorry
  exact ⟨L, R, funext L_R, funext R_L⟩
  }

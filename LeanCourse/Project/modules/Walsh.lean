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
  else if x < 1/2 then
    let m := n / 2
    if n = 0 then 1
    else walsh m (2 * x)
  else
    if n = 0 then 1
    else
      let m := n / 2
      if  n % 2 = 0 then walsh m (2 * x - 1)
      else -walsh m (2 * x - 1)
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
theorem walsh_zero (x : ℝ) (h1 :0 ≤ x) (h2: x <1 ) : walsh 0 x = 1 := by
  simp [walsh, h1,h2]


/--
Special case: Walsh function for n=1.
-/
@[simp]
theorem walsh_one_left (x : ℝ) (h1 :0 ≤ x) (h2: x < 1/2 ) : walsh 1 x =  1:= by
  simp[walsh]
  split_ifs with h_1 h_2 h_3 h_4
  · exfalso
    obtain h_l|h_r := h_1
    · linarith
    · linarith
  · exfalso
    obtain h_l|h_r := h_3
    · linarith
    · linarith
  · rfl
  · exfalso
    obtain h_l|h_r := h_4
    · push_neg at h_2
      simp_all
      linarith
    · linarith
  · exfalso
    push_neg at h_1 h_4
    linarith


@[simp]
theorem walsh_one_right (x : ℝ) (h1 :1/2 ≤ x) (h2: x < 1 ) : walsh 1 x = -1:= by
  simp[walsh]
  split_ifs with h_1 h_2 h_3 h_4
  · exfalso
    obtain h_l|h_r := h_1
    · linarith
    · linarith
  · exfalso
    obtain h_l|h_r := h_3
    · linarith
    · push_neg at h_1
      simp_all
      linarith
  · exfalso
    push_neg at h_1 h_3
    linarith
  · exfalso
    obtain h_l|h_r := h_4
    · push_neg at h_2 h_1
      simp_all
      rw[inv_le_iff_one_le_mul₀ (zero_lt_two)] at h_2
      linarith
    · linarith
  · rfl


/--
Walsh function for n being even.
-/
theorem walsh_even_left {n : ℕ}{x : ℝ}(h1 :0 ≤ x) (h2: x < 1/2 ) : walsh (2*n) x = walsh n (2 * x) := by
  conv_lhs =>
    unfold walsh
  simp
  split_ifs with h_1 h_2 h_3 h_4
  · exfalso
    obtain hl|hp := h_1
    · linarith
    · linarith
  · push_neg at h_1
    rw[h_3]
    rw[walsh_zero (2*x)]
    · linarith
    · linarith
  · rfl
  · push_neg at h_1 h_2
    rw[h_4]
    rw[walsh_zero (2*x)]
    · linarith
    · linarith
  · push_neg at h_1 h_2 h_4
    exfalso
    simp_all
    linarith


theorem walsh_even_right {n : ℕ}{x : ℝ}  (h1 :1/2 ≤ x) (h2: x < 1 ) : walsh (2*n) x = walsh n (2 * x - 1) := by
  conv_lhs =>
    unfold walsh
  simp
  split_ifs with h_1 h_2 h_3 h_4
  · exfalso
    obtain hl|hp := h_1
    · linarith
    · linarith
  · push_neg at h_1
    rw[h_3]
    rw[walsh_zero (2*x-1)]
    · linarith
    · linarith
  · push_neg at h_1 h_3
    exfalso
    simp_all
    linarith
  · push_neg at h_1 h_2
    rw[h_4]
    rw[walsh_zero (2*x-1)]
    · linarith
    · linarith
  · rfl


/--
Walsh function for n being odd.
-/

theorem walsh_odd_left {n : ℕ}{x : ℝ}(h1 :0 ≤ x) (h2: x < 1/2 ) : walsh (2*n +1) x = walsh n (2 * x) := by
  conv_lhs =>
    unfold walsh
  simp
  have h_odd0 : Odd (2 * n + 1) := by
    simp
  have h_oddp : 2*((2 * n + 1  )/2) = 2*n := by
    rw[Nat.odd_iff] at h_odd0
    rw[Nat.two_mul_odd_div_two h_odd0]
    simp
  have h_odd : (2 * n + 1) / 2 = n := by
    rw[← Nat.mul_left_inj (a:=2), mul_comm, h_oddp]
    linarith
    simp
  split_ifs with h_1 h_2 h_3
  · exfalso
    obtain hl|hp := h_1
    · linarith
    · linarith
  · push_neg at h_1
    rw[h_odd]
  · rw[h_odd]
    push_neg at h_1 h_2
    exfalso
    rw[Nat.odd_iff] at h_odd0
    linarith
  · push_neg at h_1 h_2 h_3
    rw[h_odd]
    simp_all
    linarith

theorem walsh_odd_right {n : ℕ}{x : ℝ} (h1 :1/2 ≤ x) (h2: x < 1 ) : walsh (2*n+ 1) x =- walsh n (2 * x - 1) := by
  conv_lhs =>
    unfold walsh
  simp
  have h_odd0 : Odd (2 * n + 1) := by
    simp
  have h_oddp : 2*((2 * n + 1  )/2) = 2*n := by
    rw[Nat.odd_iff] at h_odd0
    rw[Nat.two_mul_odd_div_two h_odd0]
    simp
  have h_odd : (2 * n + 1) / 2 = n := by
    rw[← Nat.mul_left_inj (a:=2), mul_comm, h_oddp]
    linarith
    simp
  split_ifs with h_1 h_2 h_3
  · exfalso
    obtain hl|hp := h_1
    · linarith
    · linarith
  · push_neg at h_1
    exfalso
    simp_all
    linarith
  · rw[h_odd]
    push_neg at h_1 h_2
    exfalso
    rw[Nat.odd_iff] at h_odd0
    linarith
  · push_neg at h_1 h_2 h_3
    rw[h_odd]


/--
Relation between Walsh function of `2n` and `2n+1`.
-/
theorem walsh_even_odd_left {n : ℕ}{x : ℝ} (h1 :0 ≤ x) (h2: x < 1/2 ): walsh (2*n) x = walsh (2*n +1) x:= by
  rw[ walsh_even_left h1 h2, walsh_odd_left h1 h2]

theorem walsh_even_odd_right {n : ℕ}{x : ℝ} (h1 :1/2 ≤ x) (h2: x < 1 ) :walsh (2*n) x = - walsh (2*n +1) x:= by
  rw[ walsh_even_right h1 h2, walsh_odd_right h1 h2]
  simp

--Nat.Bit

/--
Walsh functions are nonzero on `[0,1)`
-/
theorem walsh_in (n : ℕ) (x : ℝ): ∀ x : ℝ, 0 ≤ x ∧  x < 1 → walsh n x ≠ 0 := by
  induction' n using Nat.strong_induction_on with n ih
  intro x hx
  set k := n/2 with h_k
  by_cases hzero :n = 0
  · rw[hzero, walsh_zero]
    · linarith
    · let h1:= hx.1
      exact h1
    · let h2:= hx.2
      exact h2
  · by_cases hone : n = 1
    · rw[hone]
      by_cases h : x< 1/2
      · rw[walsh_one_left]
        · linarith
        · linarith
        · exact h
      · push_neg at h
        rw[walsh_one_right]
        · linarith
        · exact h
        · linarith
    · have hk2 : k < n := by
        push_neg at hzero
        rw[h_k]
        apply Nat.div2Induction.proof_2
        apply Nat.pos_of_ne_zero hzero
      by_cases h0 : Odd n
      · have hk1 : 2*k+1 = n := by
          rw[h_k]
          rw[mul_comm]
          apply Nat.div_two_mul_two_add_one_of_odd
          exact h0
        rw[← hk1]
        by_cases h : x<1/2
        · rw[walsh_odd_left]
          · set y:= 2* x with h_y
            have hy : 0≤ y ∧ y<1 := by
              rw[h_y]
              constructor
              · linarith
              · linarith
            exact ih k hk2 y hy
          · let h1:= hx.1
            exact h1
          · exact h
        · push_neg at h
          rw[walsh_odd_right]
          · set y:= 2* x -1 with h_y
            have hy : 0≤ y ∧ y<1 := by
              rw[h_y]
              constructor
              · linarith
              · linarith
            simp
            exact ih k hk2 y hy
          · exact h
          · let h2:= hx.2
            exact h2
      · push_neg at h0
        simp at h0
        have hk1 : 2*k = n := by
          rw[h_k]
          rw[mul_comm]
          apply Nat.div_two_mul_two_of_even
          exact h0
        rw[← hk1]
        by_cases h : x<1/2
        · rw[walsh_even_left]
          · set y:= 2* x with h_y
            have hy : 0≤ y ∧ y<1 := by
              rw[h_y]
              constructor
              · linarith
              · linarith
            exact ih k hk2 y hy
          · let h1:= hx.1
            exact h1
          · exact h
        · push_neg at h
          rw[walsh_even_right]
          · set y:= 2* x -1 with h_y
            have hy : 0≤ y ∧ y<1 := by
              rw[h_y]
              constructor
              · linarith
              · linarith
            exact ih k hk2 y hy
          · exact h
          · let h2:= hx.2
            exact h2


 /--
Walsh function is zero outside the interval `[0, 1)`.
  -/
@[simp]
theorem walsh_zero_outside_domain (n : ℕ) (x : ℝ) (h : x < 0 ∨ x ≥ 1) : walsh n x = 0 := by
simp [walsh, h]



/--
Multiplying Wlash functions of fixed `n` and different arguments.
-/
theorem mul_walsh_outside {n : ℕ} (x y : ℝ ) (h : x <0 ∨  1 ≤  x) : (walsh n x)*(walsh n y ) =  0:= by
  rw[walsh_not_in]
  simp
  exact  h

theorem mul_walsh_outside' {n : ℕ} (x y : ℝ ) (h : x <0 ∨  1 ≤  x) : (walsh n y )*(walsh n x) =  0:= by
  rw[mul_comm, mul_walsh_outside]
  exact  h

--TO NIE JEST PRAWDA!!
theorem mul_walsh {n : ℕ} (x y : ℝ ): (walsh n x)*(walsh n y ) =  (if (x <0 ∨  1 ≤  x) ∨ (y <0 ∨  1 ≤  y) then 0 else if (x < 0.5 ∧ y < 0.5) ∨ (x ≥  0.5 ∧ y ≥ 0.5) then 1 else -1) := by
  sorry

/--
Multiplying Wlash functions of fixed `n` and same arguments.
-/
theorem sqr_walsh {n : ℕ} (x : ℝ) (h1 : 0 ≤ x)(h2: x < 1) : (walsh n x)*(walsh n x) = 1 := by
  rw[mul_walsh]
  simp
  split_ifs with h_1 h_2
  · exfalso
    obtain h_l1|h_r1 :=h_1
    · linarith
    · linarith
  · rfl
  · exfalso
    push_neg at h_1 h_2
    linarith

/--
Walsh inner product definition.
-/
def walshInnerProduct (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  ∫ x in Set.Ico 0 1, f x * walsh n x

/--
Walsh functions are orthogonal.
-/


theorem walshInnermul {n m : ℕ}  : walshInnerProduct (walsh n) m = walshInnerProduct (walsh m) n := by
  simp[walshInnerProduct]
  have h1 : EqOn ((walsh n)*(walsh m)) ((walsh m)*(walsh n))  (Set.Ico 0 (1:ℝ)):= by
    rw[mul_comm]
    exact fun ⦃x⦄ ↦ congrFun rfl
  have h2 : MeasurableSet (Set.Ico 0 (1:ℝ)) := by
    simp
  --rw[MeasureTheory.setIntegral_congr h2 h1]
  sorry

theorem walsh_orthogonalityhelp {n m : ℕ} (h : n < m) : walshInnerProduct (walsh n) m = 0 := by
  simp[walshInnerProduct]
  sorry


theorem walsh_orthogonality {n m : ℕ} (h : n ≠ m) : walshInnerProduct (walsh n) m = 0 := by
  by_cases h1: n<m
  · apply walsh_orthogonalityhelp h1
  · push_neg at h1
    have h2 : m< n := by
      exact Nat.lt_of_le_of_ne h1 (id (Ne.symm h))
    rw[walshInnermul]
    apply walsh_orthogonalityhelp h2

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
  simp[walshInnerProduct]
  --rw[MeasureTheory.lintegral_const_mul]
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
  unfold walshInnerProduct
  simp
  rw[← MeasureTheory.integral_add]
  · simp[add_mul]
  · sorry
  · sorry


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

theorem binaryRepresentationSet_not_zero (n : ℕ ) (h : n >0 )  : binaryRepresentationSet n ≠  ∅ := by
  rw[gt_iff_lt, ← Nat.ne_zero_iff_zero_lt] at h
  apply Nat.ne_zero_implies_bit_true at h
  obtain ⟨ i, h_i ⟩ := h
  rw[←  mem_binaryRepresentationSet_iff ] at h_i
  simp
  intro h
  rw [h] at h_i
  exact Finset.not_mem_empty i h_i

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
  push_neg at hl
  rw [mem_binaryRepresentationSet_iff N x] at hr
  apply (mem_binaryRepresentationSet_iff (N - 2 ^ M) x).mpr ?h.mp.intro.a
  apply Nat.testBit_implies_ge at hr
  sorry
  /- maybe useful in the future apply Nat.size_le -/
  sorry
/-Nat.digit-/


theorem remove_bit1 (N M : ℕ) (h : M ∈ binaryRepresentationSet N) : binaryRepresentationSet N \ {M} = binaryRepresentationSet (N - 2^M) := by
  rw [mem_binaryRepresentationSet_iff ] at h
  ext x
  simp
  constructor
  intro h1
  rcases h1 with ⟨hr, hl⟩
  push_neg at hl
  rw [mem_binaryRepresentationSet_iff N x] at hr
  apply (mem_binaryRepresentationSet_iff (N - 2 ^ M) x).mpr ?h.mp.intro.a
  apply Nat.testBit_implies_ge at hr
  sorry
  /- maybe useful in the future apply Nat.size_le -/
  sorry


theorem binaryRepresentationSet_explicit (n :ℕ ) : ∑ k in binaryRepresentationSet n, 2^k = n := by
 /- apply Nat.eq_of_testBit_eq
  --simp[binaryRepresentationSet]
  have h1 (k m : ℕ ) : (2 ^ k).testBit m = True ↔ m= k:= by sorry
 -- have h1 (i : ℕ ) : (∑ k ∈ binaryRepresentationSet n, 2 ^ k).testBit i = ∑ k ∈ binaryRepresentationSet n,((2 ^ k).testBit i) := sorry
  intro i
  have h2 (i : ℕ ) : (∑ k ∈ binaryRepresentationSet n, 2 ^ k).testBit i = True ↔ i ∈ binaryRepresentationSet n := sorry
  by_cases h : (∑ k ∈ binaryRepresentationSet n, 2 ^ k).testBit i
  · rw[h]
    sorry
  · sorry-/
  induction' n using Nat.strong_induction_on with n ih

  sorry





theorem max_binaryRepresentationSet (n : ℕ ) (h : n >0 ) : ∃ k ∈  binaryRepresentationSet n, ∀ j > k, j ∉ binaryRepresentationSet n := by
  /-have h0 : (binaryRepresentationSet n).Nonempty := by
    apply binaryRepresentationSet_not_zero at h
    exact Finset.nonempty_iff_ne_empty.mpr h-/
  have h1 :  ∃ a, Finset.max (binaryRepresentationSet n )= a := by
    exact exists_eq'
  obtain ⟨ a , ha ⟩ := h1
  have h2 (k :ℕ ): ∀ j > k, j ∉ binaryRepresentationSet n ↔ ∀ j ∈  binaryRepresentationSet n, j≤ k := by
    sorry
  sorry

theorem min_binaryRepresentationSet (n : ℕ ) (h : n >0 ) : ∃ k ∈  binaryRepresentationSet n, ∀ j < k, j ∉ binaryRepresentationSet n := by sorry

end Walsh

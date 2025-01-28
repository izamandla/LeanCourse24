import LeanCourse.Project.modules.DyadicStructures
import LeanCourse.Project.modules.Haar
import LeanCourse.Project.modules.Walsh

open Function Set Classical
noncomputable section


/- ## Kernel-/
namespace Kernel

/--
Kernel function defined using Haar functions and binary representation sets.
-/
def kernel (N : ℕ) (x y : ℝ) : ℝ :=
    1 + ∑ m in Walsh.binaryRepresentationSet N, ∑ n in Finset.range (2^m), (Haar.haarFunctionScaled m n x) * (Haar.haarFunctionScaled m n y)


/--
The kernel function at `N = 0` is constant 1.
-/
theorem kernel_zero (x y : ℝ) : kernel 0 x y = 1 := by
  unfold kernel
  sorry


/--
Kernel function for binary powers `N = 2^m`.
-/
theorem kernel_two_pow (m : ℕ) (x y : ℝ) : kernel (2^m) x y = 1 + ∑ n in Finset.range (2^m), (Haar.haarFunctionScaled m n x) * (Haar.haarFunctionScaled m n y) := by
    sorry


end Kernel


/--
Relation between Haar function and Walsh functions.
-/

theorem walsh_haar_one (x : ℝ ) : Walsh.walsh 1 x  = Haar.haarFunction x := by
  unfold Walsh.walsh
  simp
  split_ifs with h
  sorry
  sorry
  sorry


/--
Walsh functions expressed using products of Rademacher functions.
-/
--this is not necesserly true (bc of changed definition - check!)
theorem walshRademacherRelation (n : ℕ) (x : ℝ) :
  Walsh.walsh n x = ∏ m in Walsh.binaryRepresentationSet n , Haar.rademacherFunction m x := by
  sorry

/--
Special case of Walsh-Rademacher relation for powers of two.
-/
theorem differentwalshRademacherRelation (n : ℕ) (x : ℝ) :
  Walsh.walsh (2^n) x = Haar.rademacherFunction n x := by
  sorry

theorem walshRademacherRelationresult {M N : ℕ} (h : 2^M ≤ N) (x : ℝ) :
  Walsh.walsh N x = Walsh.walsh (2^M) x * ∏ m in Walsh.binaryRepresentationSet (N - (2^M)) , Haar.rademacherFunction m x := by
  simp [walshRademacherRelation]
  have h1: Walsh.binaryRepresentationSet (2 ^ M) ∪ Walsh.binaryRepresentationSet (N - 2 ^ M)= Walsh.binaryRepresentationSet N := by
    rw[← Walsh.remove_bit]
    unfold Walsh.binaryRepresentationSet
    sorry
    sorry
  --unfold binaryRepresentationSet
  sorry


theorem fun_change_partial_sum (M N : ℕ) (f : ℝ → ℝ) (x : ℝ ) : Haar.rademacherFunction M x *(Walsh.walshFourierPartialSum (Haar.rademacherFunction M * f)  N ) x = ∑ n in Finset.range N, (∫ y in Set.Icc 0 1, (Haar.rademacherFunction M y )* f y * Walsh.walsh n y) * Haar.rademacherFunction M x * Walsh.walsh n x  := by
  sorry

/- ## Additional lemmas needed for the main result -/

/--
Lemma 3.1 (part 1).
-/
theorem lemma1_1 (M N : ℕ) (h : 2^M ≤ N ∧ N < 2^(M+1)) (f : ℝ → ℝ) (x : ℝ) :
  Walsh.walshFourierPartialSum f (2^M) x =
  ∑ k in Finset.range (2^M) , (∫ y in Set.Icc 0 1, f y * Walsh.walsh (2^M) y * (Haar.haarFunctionScaled M k y)  * Walsh.walsh (2^M) x  * (Haar.haarFunctionScaled M k x) ):=
  sorry

/--
Lemma 3.1 (part 2).
-/
theorem lemma1_2 (M N : ℕ) (h : 2^M ≤ N ∧ N < 2^(M+1)) (f : ℝ → ℝ) (x : ℝ) :
  Walsh.walshFourierPartialSum f (2^M) x =
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

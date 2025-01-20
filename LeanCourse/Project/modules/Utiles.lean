import Mathlib
import LeanCourse.Project.modules.DyadicStructures
import LeanCourse.Project.modules.Haar
import LeanCourse.Project.modules.Walsh

open Function Set Classical
noncomputable section


/- ## Kernel-/
namespace Kernel
def kernel (N : ℕ) (x y : ℝ) : ℝ :=
    1 + ∑ m in Walsh.binaryRepresentationSet N, ∑ n in Finset.range (2^m), (Haar.haarFunctionScaled m n x) * (Haar.haarFunctionScaled m n y)

theorem kernel_zero (x y : ℝ) : kernel 0 x y = 1 := by
  unfold kernel
  --apply Walsh.binaryRepresentationSet_zero
  sorry

theorem kernel_binary (N : ℕ) (x y : ℝ) (h : ∃ (m : ℕ), N = 2^m) : kernel N x y = 1 + ∑ n in Finset.range (2^m), (Haar.haarFunctionScaled m n x) * (Haar.haarFunctionScaled m n y) := by
    sorry
--co zrobić z tym m - czy muszę je wpisywać w argumentach?

end Kernel


/--
Relations between Rademacher and Walsh functions.
-/

theorem walsh_haar_one (x : ℝ ) : Walsh.walsh 1 x  = Haar.haarFunction x := by
  sorry

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
    rw[← Walsh.remove_bit]
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

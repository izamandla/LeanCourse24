--import LeanCourse.Project.modules.DyadicStructures
--import LeanCourse.Project.modules.Haar
--import LeanCourse.Project.modules.Walsh
import LeanCourse.Project.modules.Utiles


/- ## Main result -/

theorem mainresult (N : ℕ) (f : ℝ → ℝ) (x : ℝ) :
  Walsh.WalshFourierPartialSum f N x = (∫ y in Set.Icc 0 1, f y * Walsh.walsh N y * Walsh.walsh N x * Kernel.kernel N x y) := by
  sorry

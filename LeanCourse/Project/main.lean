--import LeanCourse.Project.modules.DyadicStructures
--import LeanCourse.Project.modules.Haar
--import LeanCourse.Project.modules.Walsh
import LeanCourse.Project.modules.Utiles

/-!
## Project Overview
This project aims to make first steps to prove the Walsh analogue of the Carleson-Hunt theorem
using the Linearized Metric Carleson theorem. Those steps include:
1. Defining dyadic intervals, rectangles, and related structures, and showing some coloraries about them.
2. Defining Haar, Walsh and Rademacher functions, as well as the Walsh-Fourier series and looking at the relations between them.
3. Showing the first bigger theorem needed for the main proof.
-/

/- ## Main result -/

theorem mainresult (N : ℕ) (f : ℝ → ℝ) (x : ℝ) :
  Walsh.WalshFourierPartialSum f N x = (∫ y in Set.Icc 0 1, f y * Walsh.walsh N y * Walsh.walsh N x * Kernel.kernel N x y) := by
  sorry

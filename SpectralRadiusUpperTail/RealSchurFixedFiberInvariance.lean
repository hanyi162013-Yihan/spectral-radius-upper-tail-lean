import SpectralRadiusUpperTail.RealGaussianFixedSchurBlockCount
import SpectralRadiusUpperTail.RealSchurMixedGaussianFiber
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix BigOperators

/-- For a fixed chart, changing strictly upper block entries does not
change any diagonal block, even when the chart is centered at `T`. -/
theorem realSchurFixed_diagonalBlock_fiber_const
    {n : ℕ} (c : RealSchurFixedChartIndex n)
    (ω : RealSchurMixedOrbitIndex (realSchurListBlockSize c.shape) → ℝ)
    (d : RealSchurMixedDiagonalEntry (realSchurListBlockSize c.shape) → ℝ)
    (u v : RealSchurMixedStrictUpperEntry (realSchurListBlockSize c.shape) → ℝ)
    (j : Fin c.shape.length) :
    (c.frame.T + (realSchurMixedFiberPoint _ ω d u).2.val).toSquareBlock
        (fun z : RealSchurMixedCoord (realSchurListBlockSize c.shape) => z.1) j =
      (c.frame.T + (realSchurMixedFiberPoint _ ω d v).2.val).toSquareBlock
        (fun z : RealSchurMixedCoord (realSchurListBlockSize c.shape) => z.1) j := by
  ext a b
  have hab : a.val.1 = b.val.1 := a.property.trans b.property.symm
  simp [Matrix.toSquareBlock_def, realSchurMixedFiberPoint_upper,
    realSchurMixedUpperEntryJoin, hab]

/-- The exterior root statistic is constant along every strictly upper
Gaussian fiber of a fixed real-Schur chart. -/
theorem realSchurFixedDiagonalExteriorCount_fiber_const
    {n : ℕ} (c : RealSchurFixedChartIndex n)
    (ω : RealSchurMixedOrbitIndex (realSchurListBlockSize c.shape) → ℝ)
    (d : RealSchurMixedDiagonalEntry (realSchurListBlockSize c.shape) → ℝ)
    (u v : RealSchurMixedStrictUpperEntry (realSchurListBlockSize c.shape) → ℝ)
    (r : ℝ) (i : Fin 3) :
    realSchurFixedDiagonalExteriorCount c
        (realSchurMixedFiberPoint _ ω d u) r i =
      realSchurFixedDiagonalExteriorCount c
        (realSchurMixedFiberPoint _ ω d v) r i := by
  classical
  unfold realSchurFixedDiagonalExteriorCount
  apply Finset.sum_congr rfl
  intro j _
  rw [realSchurFixed_diagonalBlock_fiber_const c ω d u v j]

/-- The local Jacobian is also constant on these fibers. -/
theorem realSchurFixed_jacobian_fiber_const
    {n : ℕ} (c : RealSchurFixedChartIndex n)
    (ω : RealSchurMixedOrbitIndex (realSchurListBlockSize c.shape) → ℝ)
    (d : RealSchurMixedDiagonalEntry (realSchurListBlockSize c.shape) → ℝ)
    (u v : RealSchurMixedStrictUpperEntry (realSchurListBlockSize c.shape) → ℝ) :
    realSchurMixedJacobianWeight (realSchurListBlockSize c.shape) c.frame.T
        (realSchurMixedFiberPoint _ ω d u) =
      realSchurMixedJacobianWeight (realSchurListBlockSize c.shape) c.frame.T
        (realSchurMixedFiberPoint _ ω d v) := by
  apply realSchurMixedJacobianWeight_eq_of_diagonal_blocks
    (realSchurListBlockSize c.shape) c.frame.T c.frame.T
    (realSchurMixedFiberPoint _ ω d u)
    (realSchurMixedFiberPoint _ ω d v) rfl
  intro j a b
  simp [realSchurMixedFiberPoint_upper, realSchurMixedUpperEntryJoin]

#print axioms realSchurFixedDiagonalExteriorCount_fiber_const
#print axioms realSchurFixed_jacobian_fiber_const
end SpectralRadiusUpperTail

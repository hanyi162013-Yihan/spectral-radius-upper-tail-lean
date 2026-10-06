import SpectralRadiusUpperTail.RealSchurFixedFiberInvariance
import SpectralRadiusUpperTail.RealSchurMixedTranslatedFiber
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped Matrix BigOperators

/-- On a complete strictly-upper fiber, the actual local Jacobian and
root count may be pulled outside the Gaussian integral. The surviving
factor is a diagonal-block Gaussian density with the exact normalizer.
The first-chart source of the global atlas need not contain such a
complete fiber; this theorem isolates the remaining domain issue. -/
theorem realSchurFixedGaussianJacobianCount_integral_fullFiber
    {n : ℕ} (c : RealSchurFixedChartIndex n)
    (ω : RealSchurMixedOrbitIndex (realSchurListBlockSize c.shape) → ℝ)
    (d : RealSchurMixedDiagonalEntry (realSchurListBlockSize c.shape) → ℝ)
    (r : ℝ) (i : Fin 3) :
    (∫ u : RealSchurMixedStrictUpperEntry
        (realSchurListBlockSize c.shape) → ℝ,
      realSchurMixedJacobianWeight (realSchurListBlockSize c.shape)
          c.frame.T (realSchurMixedFiberPoint _ ω d u) *
        realMatrixGaussianWeight
          (RealSchurMixedCoord (realSchurListBlockSize c.shape))
          (c.frame.T + (realSchurMixedFiberPoint _ ω d u).2.val) *
        (realSchurFixedDiagonalExteriorCount c
          (realSchurMixedFiberPoint _ ω d u) r i : ℝ)) =
      (realSchurMixedJacobianWeight (realSchurListBlockSize c.shape)
          c.frame.T (realSchurMixedFiberPoint _ ω d 0) *
        (realSchurFixedDiagonalExteriorCount c
          (realSchurMixedFiberPoint _ ω d 0) r i : ℝ)) *
      (Real.exp (-(∑ p : RealSchurMixedDiagonalEntry
          (realSchurListBlockSize c.shape),
            (c.frame.T p.1.1 p.1.2 + d p)^2)/2) *
        (Real.sqrt (2*Real.pi)) ^
          (Fintype.card (RealSchurMixedStrictUpperEntry
            (realSchurListBlockSize c.shape)))) := by
  have hpoint (u : RealSchurMixedStrictUpperEntry
      (realSchurListBlockSize c.shape) → ℝ) :
      realSchurMixedJacobianWeight (realSchurListBlockSize c.shape)
          c.frame.T (realSchurMixedFiberPoint _ ω d u) *
        realMatrixGaussianWeight
          (RealSchurMixedCoord (realSchurListBlockSize c.shape))
          (c.frame.T + (realSchurMixedFiberPoint _ ω d u).2.val) *
        (realSchurFixedDiagonalExteriorCount c
          (realSchurMixedFiberPoint _ ω d u) r i : ℝ) =
      (realSchurMixedJacobianWeight (realSchurListBlockSize c.shape)
          c.frame.T (realSchurMixedFiberPoint _ ω d 0) *
        (realSchurFixedDiagonalExteriorCount c
          (realSchurMixedFiberPoint _ ω d 0) r i : ℝ)) *
        realMatrixGaussianWeight
          (RealSchurMixedCoord (realSchurListBlockSize c.shape))
          (c.frame.T + (realSchurMixedFiberPoint _ ω d u).2.val) := by
    rw [realSchurFixed_jacobian_fiber_const c ω d u 0,
      realSchurFixedDiagonalExteriorCount_fiber_const c ω d u 0]
    ring
  simp_rw [hpoint]
  rw [integral_const_mul,
    realSchurMixedGaussianWeight_integral_translatedFiber
      (realSchurListBlockSize c.shape) c.frame.T c.frame.upper ω d]

#print axioms realSchurFixedGaussianJacobianCount_integral_fullFiber
end SpectralRadiusUpperTail

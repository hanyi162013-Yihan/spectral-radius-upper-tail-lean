import SpectralRadiusUpperTail.RealSchurMixedUpperGaussianIntegral
import SpectralRadiusUpperTail.RealSchurMixedDiagonalDependence
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped Matrix BigOperators

/-- Hold the angular and diagonal-block coordinates fixed and vary only
the independent strictly-upper block entries. -/
noncomputable def realSchurMixedFiberPoint
    {m : ℕ} (s : Fin m → ℕ)
    (ω : RealSchurMixedOrbitIndex s → ℝ)
    (d : RealSchurMixedDiagonalEntry s → ℝ)
    (u : RealSchurMixedStrictUpperEntry s → ℝ) :
    RealSchurMixedTangent s :=
  (ω, (realSchurMixedUpperEntryEquiv s).symm (d,u))

theorem realSchurMixedFiberPoint_upper
    {m : ℕ} (s : Fin m → ℕ)
    (ω : RealSchurMixedOrbitIndex s → ℝ)
    (d : RealSchurMixedDiagonalEntry s → ℝ)
    (u : RealSchurMixedStrictUpperEntry s → ℝ) :
    (realSchurMixedFiberPoint s ω d u).2.val =
      realSchurMixedUpperEntryJoin s d u := by
  rfl

/-- The mixed-Schur Jacobian is constant along each strict-upper fiber. -/
theorem realSchurMixedJacobianWeight_fiber_const
    {m : ℕ} (s : Fin m → ℕ)
    (ω : RealSchurMixedOrbitIndex s → ℝ)
    (d : RealSchurMixedDiagonalEntry s → ℝ)
    (u v : RealSchurMixedStrictUpperEntry s → ℝ) :
    realSchurMixedJacobianWeight s 0 (realSchurMixedFiberPoint s ω d u) =
      realSchurMixedJacobianWeight s 0 (realSchurMixedFiberPoint s ω d v) := by
  apply realSchurMixedJacobianWeight_eq_of_diagonal_blocks s 0 0
    (realSchurMixedFiberPoint s ω d u)
    (realSchurMixedFiberPoint s ω d v) rfl
  intro i a b
  simp only [zero_add, realSchurMixedFiberPoint_upper]
  simp [realSchurMixedUpperEntryJoin]

/-- For each fixed angle and diagonal array, all strict-upper Gaussian
variables integrate out exactly; the Jacobian remains outside. -/
theorem realSchurMixedGaussianJacobian_integral_upper
    {m : ℕ} (s : Fin m → ℕ)
    (ω : RealSchurMixedOrbitIndex s → ℝ)
    (d : RealSchurMixedDiagonalEntry s → ℝ) :
    (∫ u : RealSchurMixedStrictUpperEntry s → ℝ,
      realSchurMixedJacobianWeight s 0
        (realSchurMixedFiberPoint s ω d u) *
          realMatrixGaussianWeight (RealSchurMixedCoord s)
            (realSchurMixedFiberPoint s ω d u).2.val) =
      realSchurMixedJacobianWeight s 0
        (realSchurMixedFiberPoint s ω d 0) *
        (Real.exp (-(∑ p : RealSchurMixedDiagonalEntry s, (d p)^2)/2) *
          (Real.sqrt (2*Real.pi)) ^
            (Fintype.card (RealSchurMixedStrictUpperEntry s))) := by
  have hconst (u : RealSchurMixedStrictUpperEntry s → ℝ) :=
    realSchurMixedJacobianWeight_fiber_const s ω d u 0
  simp_rw [hconst, realSchurMixedFiberPoint_upper]
  rw [integral_const_mul, realSchurMixedGaussianWeight_integral_upper]

#print axioms realSchurMixedGaussianJacobian_integral_upper
end SpectralRadiusUpperTail

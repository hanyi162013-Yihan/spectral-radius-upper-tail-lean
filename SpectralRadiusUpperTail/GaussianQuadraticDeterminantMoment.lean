import SpectralRadiusUpperTail.RealQuadraticDeterminantCharpoly
import SpectralRadiusUpperTail.GaussianComplexCharpolyPoissonMoment
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped Matrix

/-- Edelman's finite-dimensional quadratic-determinant identity for an
actual iid standard *real* Gaussian matrix. This is the analytic term
in the nonreal marked-pair Jacobian, before any eigenvalue counting. -/
theorem gaussian_real_quadratic_det_poisson_moment
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x y : ℝ) :
    (∫ z : ι × ι → ℝ,
      (((Matrix.of z.curry) - x • 1)^2 + y^2 • 1).det
      ∂Measure.pi (fun _ => standardNormal)) =
      ((Fintype.card ι).factorial : ℝ) *
        ginibreExpPartial (Fintype.card ι+1) (x^2+y^2) := by
  classical
  simp_rw [real_quadratic_det_eq_charpoly_normSq]
  rw [gaussian_real_complex_charpoly_poisson_moment]
  have hnorm : Complex.normSq ((x : ℂ) + (y : ℂ)*Complex.I) =
      x^2+y^2 := by
    simp [Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im]
    ring
  rw [hnorm]

#print axioms gaussian_real_quadratic_det_poisson_moment
end SpectralRadiusUpperTail

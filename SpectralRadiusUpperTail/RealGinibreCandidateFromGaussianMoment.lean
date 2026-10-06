import SpectralRadiusUpperTail.GaussianQuadraticDeterminantMoment
import SpectralRadiusUpperTail.RealGinibreNonrealDensityAt
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped Matrix

/-- The Poisson factor in the candidate nonreal one-point intensity is
exactly an actual iid real-Gaussian quadratic-determinant expectation.
The separate geometric task is to identify this candidate intensity with
the matrix's eigenvalue counting measure. -/
theorem realGinibreNonrealDensityAt_eq_gaussian_quadratic_moment
    (n : ℕ) (hn : 2 ≤ n) (z : ℂ) :
    realGinibreNonrealDensityAt n z =
      (n : ℝ)/Real.pi *
        gaussianErfcCorrection (Real.sqrt (2*(n : ℝ))*|z.im|) *
        (Real.exp (-(n : ℝ)*‖z‖^2) *
          ((∫ a : Fin (n-2) × Fin (n-2) → ℝ,
            (((Matrix.of a.curry) -
              (Real.sqrt (n : ℝ)*z.re) • 1)^2 +
              (Real.sqrt (n : ℝ)*z.im)^2 • 1).det
              ∂Measure.pi (fun _ => standardNormal)) /
            ((n-2).factorial : ℝ))) := by
  have hnR : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have hz : z.re^2+z.im^2 = ‖z‖^2 := by
    calc
      _ = Complex.normSq z := by rw [Complex.normSq_apply]; ring
      _ = _ := Complex.normSq_eq_norm_sq z
  have hxy :
      (Real.sqrt (n : ℝ)*z.re)^2 +
        (Real.sqrt (n : ℝ)*z.im)^2 =
      (n : ℝ)*‖z‖^2 := by
    calc
      _ = (Real.sqrt (n : ℝ))^2*(z.re^2+z.im^2) := by ring
      _ = (n : ℝ)*‖z‖^2 := by
        rw [Real.sq_sqrt hnR, hz]
  have hm := gaussian_real_quadratic_det_poisson_moment
    (ι := Fin (n-2))
    (Real.sqrt (n : ℝ)*z.re) (Real.sqrt (n : ℝ)*z.im)
  simp only [Fintype.card_fin] at hm
  have hidx : n-2+1 = n-1 := by omega
  rw [hidx, hxy] at hm
  unfold realGinibreNonrealDensityAt realGinibreNonrealDensity
  rw [hm]
  have hfact : ((n-2).factorial : ℝ) ≠ 0 := by positivity
  field_simp [hfact]

#print axioms realGinibreNonrealDensityAt_eq_gaussian_quadratic_moment
end SpectralRadiusUpperTail

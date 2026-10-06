import SpectralRadiusUpperTail.GaussianWeightedPrincipalMinorParseval
import Mathlib.Data.Complex.BigOperators
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped Matrix BigOperators

/-- The real Gaussian principal minors remain orthogonal when weighted by
complex scalars. This is the finite-dimensional determinant calculation
needed for the nonreal one-point function. -/
theorem gaussian_complex_weighted_principalMinor_parseval
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : Finset ι → ℂ) :
    Integrable (fun z : ι × ι → ℝ =>
      Complex.normSq
        (∑ s : Finset ι, a s *
          (((Matrix.of z.curry).submatrix
            (Subtype.val : s → ι) (Subtype.val : s → ι)).det : ℂ)))
      (Measure.pi (fun _ => standardNormal)) ∧
    (∫ z : ι × ι → ℝ,
      Complex.normSq
        (∑ s : Finset ι, a s *
          (((Matrix.of z.curry).submatrix
            (Subtype.val : s → ι) (Subtype.val : s → ι)).det : ℂ))
      ∂Measure.pi (fun _ => standardNormal)) =
      ∑ s : Finset ι, Complex.normSq (a s) * (s.card.factorial : ℝ) := by
  classical
  let d (s : Finset ι) (z : ι × ι → ℝ) : ℝ :=
    ((Matrix.of z.curry).submatrix
      (Subtype.val : s → ι) (Subtype.val : s → ι)).det
  have hre (z : ι × ι → ℝ) :
      (∑ s : Finset ι, a s * (d s z : ℂ)).re =
        ∑ s : Finset ι, (a s).re * d s z := by
    simp [Complex.re_sum, Complex.mul_re]
  have him (z : ι × ι → ℝ) :
      (∑ s : Finset ι, a s * (d s z : ℂ)).im =
        ∑ s : Finset ι, (a s).im * d s z := by
    simp [Complex.im_sum, Complex.mul_im]
  have hnorm (z : ι × ι → ℝ) :
      Complex.normSq (∑ s : Finset ι, a s * (d s z : ℂ)) =
        (∑ s : Finset ι, (a s).re * d s z)^2 +
        (∑ s : Finset ι, (a s).im * d s z)^2 := by
    rw [Complex.normSq_apply, hre, him]
    ring
  have hR := gaussian_weighted_principalMinor_parseval
    (ι := ι) (fun s => (a s).re)
  have hI := gaussian_weighted_principalMinor_parseval
    (ι := ι) (fun s => (a s).im)
  change Integrable (fun z =>
      Complex.normSq (∑ s : Finset ι, a s * (d s z : ℂ)))
      (Measure.pi (fun _ => standardNormal)) ∧
    (∫ z, Complex.normSq
      (∑ s : Finset ι, a s * (d s z : ℂ))
      ∂Measure.pi (fun _ => standardNormal)) =
      ∑ s : Finset ι, Complex.normSq (a s) * (s.card.factorial : ℝ)
  simp_rw [hnorm]
  constructor
  · exact hR.1.add hI.1
  · rw [integral_add hR.1 hI.1, hR.2, hI.2,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s hs
    rw [Complex.normSq_apply]
    ring

#print axioms gaussian_complex_weighted_principalMinor_parseval
end SpectralRadiusUpperTail

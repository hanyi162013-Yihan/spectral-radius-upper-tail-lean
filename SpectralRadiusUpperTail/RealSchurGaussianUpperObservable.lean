import SpectralRadiusUpperTail.RealSchurStrictUpperGaussianInvariance
import SpectralRadiusUpperTail.RealSchurBlockUpperConjugation
import SpectralRadiusUpperTail.RealSchurMixedCodeClassFiber

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped Matrix ENNReal BigOperators

noncomputable def realSchurGaussianUpperIntegral {m : ℕ} (s : Fin m → ℕ)
    (H : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ → ℝ≥0∞)
    (d : RealSchurMixedDiagonalEntry s → ℝ) : ℝ≥0∞ :=
  ∫⁻ u : RealSchurMixedStrictUpperEntry s → ℝ,
    ENNReal.ofReal (Real.exp (-(∑ p, (u p)^2)/2)) * H (realSchurMixedUpperEntryJoin s d u)

theorem realSchurGaussianUpperIntegral_measurable {m : ℕ} (s : Fin m → ℕ)
    (H : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ → ℝ≥0∞)
    (hH : Measurable H) : Measurable (realSchurGaussianUpperIntegral s H) := by
  have hw : Measurable (fun z : (RealSchurMixedDiagonalEntry s → ℝ) ×
      (RealSchurMixedStrictUpperEntry s → ℝ) =>
      ENNReal.ofReal (Real.exp (-(∑ p, (z.2 p)^2)/2))) := by fun_prop
  have h := hw.mul (hH.comp (realSchurMixedUpperEntryJoin_continuous s).measurable)
  exact h.lintegral_prod_right'

/-- After integrating all strict-upper Gaussian entries, an invariant
matrix observable becomes invariant under separate rotations within
the diagonal blocks. This justifies applying the full pair-block formula. -/
theorem realSchurGaussianUpperIntegral_conjugation
    {m : ℕ} (s : Fin m → ℕ)
    (W : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ) (hW : Wᵀ*W=1)
    (hoff : ∀ i j : RealSchurMixedCoord s, i.1 ≠ j.1 → W i j=0)
    (H : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ → ℝ≥0∞)
    (hH : Measurable H) (hInv : ∀ A, H (W*A*Wᵀ)=H A)
    (d : RealSchurMixedDiagonalEntry s → ℝ) :
    realSchurGaussianUpperIntegral s H (realSchurMixedDiagonalConjugation s W d) =
      realSchurGaussianUpperIntegral s H d := by
  let d' := realSchurMixedDiagonalConjugation s W d
  let g := fun u : RealSchurMixedStrictUpperEntry s → ℝ => H (realSchurMixedUpperEntryJoin s d' u)
  have hj : Continuous (fun u : RealSchurMixedStrictUpperEntry s → ℝ =>
      realSchurMixedUpperEntryJoin s d' u) :=
    (realSchurMixedUpperEntryJoin_continuous s).comp
      ((continuous_const : Continuous (fun _ : RealSchurMixedStrictUpperEntry s → ℝ => d')).prodMk continuous_id)
  have hg : Measurable g := hH.comp hj.measurable
  have h := realSchurMixedStrictUpperGaussian_conjugation s W hW hoff g hg
  change (∫⁻ u, ENNReal.ofReal (Real.exp (-(∑ p, (u p)^2)/2)) * g u) = _
  rw [← h]
  apply lintegral_congr
  intro u
  change ENNReal.ofReal (Real.exp (-(∑ p, (u p)^2)/2)) *
    H (realSchurMixedUpperEntryJoin s (realSchurMixedDiagonalConjugation s W d)
      (realSchurMixedStrictUpperConjugationLinear s W u)) = _
  rw [realSchurMixedUpperEntryJoin_conjugation s W hoff d u,hInv]

#print axioms realSchurGaussianUpperIntegral_measurable
#print axioms realSchurGaussianUpperIntegral_conjugation
end SpectralRadiusUpperTail

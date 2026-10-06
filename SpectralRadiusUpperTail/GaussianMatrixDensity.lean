import SpectralRadiusUpperTail.PiRealDensity
import SpectralRadiusUpperTail.GaussianMatrixWeight
import SpectralRadiusUpperTail.GaussianRegressionMatrix
import SpectralRadiusUpperTail.FiniteRowSumLaw

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators ENNReal
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂] {n : ℕ}

lemma gaussianTiltedMatrixLaw_density (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (a : ℝ) (ha : 0 < a) (v : ℕ → 𝕂) (t : Fin n → 𝕂) :
    gaussianTiltedMatrixLaw μ a v t =
      (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).withDensity
        (fun x => ENNReal.ofReal (gaussianMatrixWeight a (fun j : Fin n => v j.val) t x /
          ∏ i : Fin n, gaussianFiniteNormalizer μ a (fun j : Fin n => v j.val) (t i))) := by
  let f := fun i (x : Fin n → 𝕂) =>
    Real.exp (-‖t i-∑ j : Fin n, v j.val*x j‖^2/a)/
      gaussianFiniteNormalizer μ a (fun j : Fin n => v j.val) (t i)
  have hi : ∀ i, Integrable (f i) (Measure.pi (fun _ : Fin n => μ)) := by
    intro i
    exact (soft_exponential_integrable _ _ (by fun_prop) (fun _ => sq_nonneg _) a ha).div_const _
  have hn : ∀ i x, 0 ≤ f i x := by
    intro i x
    exact div_nonneg (Real.exp_nonneg _) (gaussianFiniteNormalizer_bounds μ a ha _ _).1
  have hh := pi_withDensity_ofReal (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ)) f hi hn
  rw [gaussianTiltedMatrixLaw]
  change Measure.pi (fun i => (Measure.pi (fun _ : Fin n => μ)).withDensity
    (fun x => ENNReal.ofReal (f i x))) = _
  rw [← hh]
  congr 1
  funext x
  congr 1
  dsimp only [f]
  rw [Finset.prod_div_distrib,← gaussianMatrixWeight_eq_product]

#print axioms gaussianTiltedMatrixLaw_density
end SpectralRadiusUpperTail

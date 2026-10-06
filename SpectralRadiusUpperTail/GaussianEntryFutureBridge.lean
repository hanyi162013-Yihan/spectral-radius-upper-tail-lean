import SpectralRadiusUpperTail.GaussianEntryKernel
import SpectralRadiusUpperTail.GaussianFutureConvolution

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators ENNReal
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂]

lemma gaussianFutureWeight_eq_finiteNormalizer (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (v : ℕ → 𝕂) (N : ℕ) (a : ℝ) (ha : 0 < a) (s : 𝕂) :
    (futureWeight μ (fun i x => v i*x) (gaussianSoftWeight a) N s).toReal =
      gaussianFiniteNormalizer μ a (fun i : Fin N => v i.val) s := by
  have he : iidRowSumLaw μ v N = finiteRowSumLaw μ (fun i : Fin N => v i.val) := rfl
  rw [gaussianFutureWeight_eq_convolution μ v N a ha, he,
    ← gaussianFiniteNormalizer_eq_convolution,
    ENNReal.toReal_ofReal (gaussianFiniteNormalizer_bounds μ a ha _ _).1]

/-- The entry law used in the regression estimate is exactly the normalized
future-likelihood law used in the existing coupling and conditional-tail theorems. -/
theorem gaussianEntryLaw_eq_future_likelihood (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (hm : (∫ x : 𝕂, x ∂μ) = 0)
    (hvar : (∫ x : 𝕂, ‖x‖^2 ∂μ) = 1)
    (v : ℕ → 𝕂) (N : ℕ) (a : ℝ) (ha : 0 < a) (b s : 𝕂)
    (hv : ‖b‖^2+∑ i : Fin N, ‖v i.val‖^2 ≤ 1) :
    let W := futureWeight μ (fun i x => v i*x) (gaussianSoftWeight a) N
    let g := fun x : 𝕂 => (W (s-b*x)).toReal/(W s).toReal
    gaussianEntryLaw μ a (fun i : Fin N => v i.val) b s =
      μ.withDensity (fun x => ENNReal.ofReal (g x/(∫ y, g y ∂μ))) := by
  dsimp only
  simp_rw [gaussianFutureWeight_eq_finiteNormalizer μ v N a ha]
  have hv' : ∑ i : Fin N, ‖v i.val‖^2 ≤ 1 := by nlinarith [sq_nonneg ‖b‖]
  have hA : 0 < gaussianFiniteNormalizer μ a (fun i : Fin N => v i.val) s :=
    (Real.exp_pos _).trans_le
      (gaussianFiniteNormalizer_lower μ hX hm hvar a ha _ hv' s ‖s‖ le_rfl)
  have hB : 0 < gaussianEntryNormalizer μ a (fun i : Fin N => v i.val) b s :=
    (Real.exp_pos _).trans_le
      (gaussianEntryNormalizer_lower μ hX hm hvar a ha _ b s hv ‖s‖ le_rfl)
  simp_rw [integral_div]
  unfold gaussianEntryLaw
  congr 1
  funext x
  congr 1
  change _ = _/(_/gaussianFiniteNormalizer μ a (fun i : Fin N => v i.val) s)
  change _ = (_/gaussianFiniteNormalizer μ a (fun i : Fin N => v i.val) s)/
    (gaussianEntryNormalizer μ a (fun i : Fin N => v i.val) b s/
      gaussianFiniteNormalizer μ a (fun i : Fin N => v i.val) s)
  field_simp

#print axioms gaussianEntryLaw_eq_future_likelihood
end SpectralRadiusUpperTail

import SpectralRadiusUpperTail.RevealedWeights
import Mathlib.Analysis.RCLike.Basic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal BigOperators

section General
variable {α E : Type*} [MeasurableSpace α] [MeasurableSpace E]
  [AddCommGroup E] [MeasurableAdd₂ E] [MeasurableSub₂ E]

/-- The recursively defined future weight is the actual product-integral normalizer. -/
theorem futureWeight_eq_product_integral (μ : Measure α) [IsProbabilityMeasure μ]
    (f : ℕ → α → E) (w : E → ℝ≥0∞) (hf : ∀ n, Measurable (f n)) (hw : Measurable w)
    (hpos : ∀ s, 0 < w s) (hle : ∀ s, w s ≤ 1) (N : ℕ) (t : E) :
    futureWeight μ f w N t =
      ∫⁻ s, w (t-∑ i : Fin N, f i.val (s i)) ∂Measure.pi (fun _ : Fin N => μ) := by
  have hc0 := ne_of_gt (futureWeight_pos μ f w hf hw hpos N t)
  have hct := ne_top_of_le_ne_top ENNReal.one_ne_top (futureWeight_le_one μ f w hle N t)
  obtain ⟨Γ, hΓ, hfirst, _⟩ := softWeight_coupling_exists μ f w hf hw hpos hle N t
  letI : IsProbabilityMeasure Γ := hΓ
  have hm : Measurable (coordinateVector (@Prod.fst α α) N) :=
    measurable_coordinateVector Prod.fst measurable_fst N
  letI : IsProbabilityMeasure (Γ.map (coordinateVector (@Prod.fst α α) N)) :=
    Measure.isProbabilityMeasure_map hm.aemeasurable
  have hmass := measure_univ (μ := Γ.map (coordinateVector (@Prod.fst α α) N))
  rw [hfirst, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at hmass
  simp only [div_eq_mul_inv] at hmass
  rw [lintegral_mul_const' _ _ (ENNReal.inv_ne_top.mpr hc0)] at hmass
  exact ((ENNReal.div_eq_one_iff hc0 hct).mp hmass).symm

end General

section Scalar
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂]

noncomputable def gaussianRowNormalizer (μ : Measure 𝕂) (v : ℕ → 𝕂)
    (a : ℝ) (N : ℕ) (t : 𝕂) : ℝ≥0∞ :=
  ∫⁻ s, gaussianSoftWeight a (t-∑ i : Fin N, v i.val * s i)
    ∂Measure.pi (fun _ : Fin N => μ)

lemma gaussianRowNormalizer_eq_future (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (v : ℕ → 𝕂) (a : ℝ) (ha : 0 < a) (N : ℕ) (t : 𝕂) :
    gaussianRowNormalizer μ v a N t =
      futureWeight μ (fun i x => v i*x) (gaussianSoftWeight a) N t := by
  exact (futureWeight_eq_product_integral μ (fun i x => v i*x) (gaussianSoftWeight a)
    (fun _ => (continuous_const.mul continuous_id).measurable)
    (gaussianSoftWeight_measurable a) (gaussianSoftWeight_pos a)
    (gaussianSoftWeight_le_one a ha) N t).symm

lemma gaussianRowNormalizer_pos (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (v : ℕ → 𝕂) (a : ℝ) (ha : 0 < a) (N : ℕ) (t : 𝕂) :
    0 < gaussianRowNormalizer μ v a N t := by
  rw [gaussianRowNormalizer_eq_future μ v a ha]
  exact futureWeight_pos μ _ _ (fun _ => (continuous_const.mul continuous_id).measurable)
    (gaussianSoftWeight_measurable a) (gaussianSoftWeight_pos a) N t

/-- The first marginal is exactly the Gaussian-soft tilted product measure;
the second is the complete original iid product law. No entry density is assumed. -/
theorem gaussianRow_coupling_exists (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (v : ℕ → 𝕂) (a : ℝ) (ha : 0 < a) (N : ℕ) (t : 𝕂) :
    ∃ Γ : Measure (Fin N → 𝕂 × 𝕂), IsProbabilityMeasure Γ ∧
      Γ.map (coordinateVector Prod.fst N) =
        (Measure.pi (fun _ : Fin N => μ)).withDensity
          (fun s => gaussianSoftWeight a (t-∑ i : Fin N, v i.val*s i) /
            gaussianRowNormalizer μ v a N t) ∧
      Γ.map (comparatorVector N) = Measure.pi (fun _ : Fin N => μ) := by
  rw [gaussianRowNormalizer_eq_future μ v a ha]
  exact softWeight_coupling_exists μ (fun i x => v i*x) (gaussianSoftWeight a)
    (fun _ => (continuous_const.mul continuous_id).measurable)
    (gaussianSoftWeight_measurable a) (gaussianSoftWeight_pos a)
    (gaussianSoftWeight_le_one a ha) N t

end Scalar
#print axioms futureWeight_eq_product_integral
#print axioms gaussianRow_coupling_exists
end SpectralRadiusUpperTail

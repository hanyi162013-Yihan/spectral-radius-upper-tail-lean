import SpectralRadiusUpperTail.GaussianEntryKernel

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators ENNReal
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂] {N : ℕ}

/-- The full vector mean of the actual entry law is its weighted numerator
multiplied by the inverse of its actual normalizer. -/
theorem gaussianEntryLaw_mean_eq (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (a : ℝ) (ha : 0 < a)
    (v : Fin N → 𝕂) (b s : 𝕂) (hB : 0 < gaussianEntryNormalizer μ a v b s) :
    (∫ x : 𝕂, x ∂gaussianEntryLaw μ a v b s) =
      (gaussianEntryNormalizer μ a v b s)⁻¹ •
        (∫ x : 𝕂, gaussianFiniteNormalizer μ a v (s-b*x) • x ∂μ) := by
  rw [gaussianEntryLaw, integral_withDensity_eq_integral_toReal_smul
    ((gaussianEntry_weight_measurable μ hX a ha v b s).div_const _).ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (div_nonneg
    (gaussianFiniteNormalizer_bounds μ a ha v _).1 hB.le)]
  simp_rw [div_eq_inv_mul, mul_smul]
  exact integral_smul _ _

lemma gaussianEntryNumerator_continuous (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (a : ℝ) (ha : 0 < a)
    (v : Fin N → 𝕂) (b : 𝕂) :
    Continuous (fun s : 𝕂 => ∫ x : 𝕂, gaussianFiniteNormalizer μ a v (s-b*x) • x ∂μ) := by
  have hA := gaussianFiniteNormalizer_continuous μ hX a ha v
  apply continuous_of_dominated (bound := fun x : 𝕂 => ‖x‖)
  · intro s
    exact (((hA.comp (by fun_prop)).smul continuous_id).aestronglyMeasurable)
  · intro s
    filter_upwards [] with x
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (gaussianFiniteNormalizer_bounds μ a ha v _).1]
    exact (mul_le_mul_of_nonneg_right
      (gaussianFiniteNormalizer_bounds μ a ha v _).2 (norm_nonneg x)).trans_eq (one_mul _)
  · exact (hX.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)).norm
  · filter_upwards [] with x
    exact (hA.comp (by fun_prop)).smul continuous_const

lemma gaussianEntryNormalizer_continuous (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (a : ℝ) (ha : 0 < a)
    (v : Fin N → 𝕂) (b : 𝕂) : Continuous (gaussianEntryNormalizer μ a v b) := by
  have he : gaussianEntryNormalizer μ a v b = gaussianFiniteNormalizer μ a (Fin.cons b v) := by
    funext s
    exact gaussianEntryNormalizer_eq_cons μ a ha v b s
  rw [he]
  exact gaussianFiniteNormalizer_continuous μ hX a ha _

/-- Positivity at every target, together with domination by the integrable
entry norm, gives continuity of the actual conditional mean. -/
theorem gaussianEntryLaw_mean_continuous (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (a : ℝ) (ha : 0 < a)
    (v : Fin N → 𝕂) (b : 𝕂) (hB : ∀ s, 0 < gaussianEntryNormalizer μ a v b s) :
    Continuous (fun s : 𝕂 => ∫ x : 𝕂, x ∂gaussianEntryLaw μ a v b s) := by
  simp_rw [gaussianEntryLaw_mean_eq μ hX a ha v b _ (hB _)]
  exact ((gaussianEntryNormalizer_continuous μ hX a ha v b).inv₀
    (fun s => (hB s).ne')).smul (gaussianEntryNumerator_continuous μ hX a ha v b)

/-- The established Jensen lower bound supplies positivity for every target;
no measurability assumption on the desired mean is needed. -/
theorem gaussianEntryLaw_mean_continuous_of_energy (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (hm : (∫ x : 𝕂, x ∂μ) = 0)
    (hvar : (∫ x : 𝕂, ‖x‖^2 ∂μ) = 1) (a : ℝ) (ha : 0 < a)
    (v : Fin N → 𝕂) (b : 𝕂) (hv : ‖b‖^2+∑ i, ‖v i‖^2 ≤ 1) :
    Continuous (fun s : 𝕂 => ∫ x : 𝕂, x ∂gaussianEntryLaw μ a v b s) := by
  apply gaussianEntryLaw_mean_continuous μ hX a ha v b
  intro s
  exact (Real.exp_pos _).trans_le
    (gaussianEntryNormalizer_lower μ hX hm hvar a ha v b s hv ‖s‖ le_rfl)

#print axioms gaussianEntryLaw_mean_eq
#print axioms gaussianEntryNumerator_continuous
#print axioms gaussianEntryLaw_mean_continuous_of_energy
end SpectralRadiusUpperTail

import SpectralRadiusUpperTail.FiniteRowSumLaw
import SpectralRadiusUpperTail.ConditionalLinearTaylor
import SpectralRadiusUpperTail.TiltedEnergy
import SpectralRadiusUpperTail.DensityCoupling

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators ENNReal
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂] {N : ℕ}

noncomputable def gaussianEntryNormalizer (μ : Measure 𝕂) (a : ℝ)
    (v : Fin N → 𝕂) (b s : 𝕂) : ℝ :=
  ∫ x : 𝕂, gaussianFiniteNormalizer μ a v (s-b*x) ∂μ

noncomputable def gaussianEntryLaw (μ : Measure 𝕂) (a : ℝ)
    (v : Fin N → 𝕂) (b s : 𝕂) : Measure 𝕂 :=
  μ.withDensity (fun x => ENNReal.ofReal
    (gaussianFiniteNormalizer μ a v (s-b*x)/gaussianEntryNormalizer μ a v b s))

/-- Actual entry/future product integration identifies the conditional denominator. -/
theorem gaussianEntryNormalizer_eq_cons (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (a : ℝ) (ha : 0 < a) (v : Fin N → 𝕂) (b s : 𝕂) :
    gaussianEntryNormalizer μ a v b s = gaussianFiniteNormalizer μ a (Fin.cons b v) s := by
  have hb (z : 𝕂) : |Real.exp (-‖z‖^2/a)| ≤ 1 := by
    rw [abs_of_nonneg (Real.exp_nonneg _)]
    exact Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (sq_nonneg _)) ha.le)
  have hh := product_sum_integral_succ N (fun _ : Fin (N+1) => μ)
    (fun (i : Fin (N+1)) (x : 𝕂) => -((Fin.cons b v : Fin (N+1) → 𝕂) i*x))
    (fun _ => by fun_prop)
    (fun z : 𝕂 => Real.exp (-‖z‖^2/a)) (by fun_prop) 1 hb s
  simpa only [gaussianEntryNormalizer, gaussianFiniteNormalizer, Fin.cons_zero, Fin.cons_succ,
    Finset.sum_neg_distrib, ← sub_eq_add_neg] using hh.symm

lemma gaussianEntryNormalizer_lower (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (hm : (∫ x : 𝕂, x ∂μ) = 0)
    (hvar : (∫ x : 𝕂, ‖x‖^2 ∂μ) = 1) (a : ℝ) (ha : 0 < a)
    (v : Fin N → 𝕂) (b s : 𝕂) (hv : ‖b‖^2+∑ i, ‖v i‖^2 ≤ 1)
    (K : ℝ) (hs : ‖s‖ ≤ K) :
    Real.exp (-(K^2+1)/a) ≤ gaussianEntryNormalizer μ a v b s := by
  rw [gaussianEntryNormalizer_eq_cons μ a ha]
  apply gaussianFiniteNormalizer_lower μ hX hm hvar a ha _ _ s K hs
  simpa only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] using hv

lemma gaussianEntry_weight_measurable (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (a : ℝ) (ha : 0 < a)
    (v : Fin N → 𝕂) (b s : 𝕂) :
    Measurable (fun x : 𝕂 => gaussianFiniteNormalizer μ a v (s-b*x)) :=
  (gaussianFiniteNormalizer_continuous μ hX a ha v).measurable.comp (by fun_prop)

/-- The normalized density is an actual probability measure whenever its
strictly positive denominator is supplied by the proved Jensen bound. -/
lemma gaussianEntryLaw_probability (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (a : ℝ) (ha : 0 < a)
    (v : Fin N → 𝕂) (b s : 𝕂) (hB : 0 < gaussianEntryNormalizer μ a v b s) :
    IsProbabilityMeasure (gaussianEntryLaw μ a v b s) := by
  have hf := gaussianEntry_weight_measurable μ hX a ha v b s
  have hb (x : 𝕂) : |gaussianFiniteNormalizer μ a v (s-b*x)| ≤ 1 := by
    rw [abs_of_nonneg (gaussianFiniteNormalizer_bounds μ a ha v _).1]
    exact (gaussianFiniteNormalizer_bounds μ a ha v _).2
  have hi := (bounded_weight_projection_integrable μ hX _ hf hb (0 : 𝕂)).1
  apply normalizedDensity_probability
  rw [← ofReal_integral_eq_lintegral_ofReal (hi.div_const _)
    (Filter.Eventually.of_forall (fun x => div_nonneg
      (gaussianFiniteNormalizer_bounds μ a ha v _).1 hB.le)), integral_div]
  change ENNReal.ofReal (gaussianEntryNormalizer μ a v b s/gaussianEntryNormalizer μ a v b s) = 1
  rw [div_self hB.ne', ENNReal.ofReal_one]

lemma gaussianEntryLaw_id_integrable (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (a : ℝ) (ha : 0 < a)
    (v : Fin N → 𝕂) (b s : 𝕂) (hB : 0 < gaussianEntryNormalizer μ a v b s) :
    Integrable (fun x : 𝕂 => x) (gaussianEntryLaw μ a v b s) := by
  have hd := boundedDensity_le_smul μ
    (fun x => gaussianFiniteNormalizer μ a v (s-b*x)/gaussianEntryNormalizer μ a v b s)
    (1/gaussianEntryNormalizer μ a v b s) (fun x =>
      div_le_div_of_nonneg_right (gaussianFiniteNormalizer_bounds μ a ha v _).2 hB.le)
  exact ((hX.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)).smul_measure
    ENNReal.ofReal_ne_top).mono_measure hd

/-- An actual conditional expectation is the ratio of the actual weighted
numerator and the actual entry/future denominator. -/
theorem gaussianEntryLaw_mean_projection (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (a : ℝ) (ha : 0 < a)
    (v : Fin N → 𝕂) (b s w : 𝕂) (hB : 0 < gaussianEntryNormalizer μ a v b s) :
    inner ℝ w (∫ x : 𝕂, x ∂gaussianEntryLaw μ a v b s) =
      (∫ x : 𝕂, inner ℝ w x*gaussianFiniteNormalizer μ a v (s-b*x) ∂μ)/
        gaussianEntryNormalizer μ a v b s := by
  rw [← integral_inner (gaussianEntryLaw_id_integrable μ hX a ha v b s hB)]
  rw [gaussianEntryLaw, integral_withDensity_eq_integral_toReal_smul
    ((gaussianEntry_weight_measurable μ hX a ha v b s).div_const _).ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (div_nonneg
    (gaussianFiniteNormalizer_bounds μ a ha v _).1 hB.le), smul_eq_mul]
  have he (x : 𝕂) :
      gaussianFiniteNormalizer μ a v (s-b*x)/gaussianEntryNormalizer μ a v b s*inner ℝ w x =
        (inner ℝ w x*gaussianFiniteNormalizer μ a v (s-b*x))/gaussianEntryNormalizer μ a v b s := by ring
  simp_rw [he]
  rw [integral_div]

#print axioms gaussianEntryNormalizer_eq_cons
#print axioms gaussianEntryLaw_probability
#print axioms gaussianEntryLaw_mean_projection
end SpectralRadiusUpperTail

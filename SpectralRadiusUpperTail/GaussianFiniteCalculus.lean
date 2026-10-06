import SpectralRadiusUpperTail.GaussianDirectionalIntegration
import SpectralRadiusUpperTail.RowNormalizerBound
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂] {N : ℕ}

noncomputable def gaussianFiniteNormalizer (μ : Measure 𝕂) (a : ℝ) (v : Fin N → 𝕂) (s : 𝕂) : ℝ :=
  ∫ x : Fin N → 𝕂, Real.exp (-‖s-∑ i, v i*x i‖^2/a) ∂Measure.pi (fun _ => μ)

noncomputable def gaussianFiniteDirectional (μ : Measure 𝕂) (a : ℝ)
    (v : Fin N → 𝕂) (w s : 𝕂) : ℝ :=
  ∫ x : Fin N → 𝕂, gaussianDirectional a w (s-∑ i, v i*x i) ∂Measure.pi (fun _ => μ)

lemma gaussianFiniteNormalizer_hasDerivAt (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (a : ℝ) (ha : 0 < a) (v : Fin N → 𝕂) (s w : 𝕂) (t : ℝ) :
    HasDerivAt (fun u : ℝ => gaussianFiniteNormalizer μ a v (s+u • w))
      (gaussianFiniteDirectional μ a v w (s+t • w)) t := by
  exact gaussian_shift_integral_hasDerivAt (Measure.pi (fun _ : Fin N => μ))
    (fun x => ∑ i, v i*x i) (measurable_finite_sum _ (fun _ => by fun_prop)) a ha s w t

lemma gaussianFiniteDirectional_bound (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (a : ℝ) (ha : 0 < a) (v : Fin N → 𝕂) (w s : 𝕂) :
    |gaussianFiniteDirectional μ a v w s| ≤ (2/a)*(1+a)*‖w‖ := by
  have hh := norm_integral_le_of_norm_le_const
    (μ := Measure.pi (fun _ : Fin N => μ))
    (f := fun x : Fin N → 𝕂 => gaussianDirectional a w (s-∑ i, v i*x i))
    (Filter.Eventually.of_forall (fun x => by
      simpa only [Real.norm_eq_abs] using gaussianDirectional_bound a ha w (s-∑ i, v i*x i)))
  simpa only [gaussianFiniteDirectional, Real.norm_eq_abs, probReal_univ, mul_one] using hh

/-- Jensen supplies a common positive lower bound on every compact target set,
for all finite coefficient families of energy at most one. -/
lemma gaussianFiniteNormalizer_lower (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (hm : (∫ x : 𝕂, x ∂μ) = 0)
    (hvar : (∫ x : 𝕂, ‖x‖^2 ∂μ) = 1)
    (a : ℝ) (ha : 0 < a) (v : Fin N → 𝕂) (hv : ∑ i, ‖v i‖^2 ≤ 1)
    (s : 𝕂) (K : ℝ) (hs : ‖s‖ ≤ K) :
    Real.exp (-(K^2+1)/a) ≤ gaussianFiniteNormalizer μ a v s := by
  have hK : 0 ≤ K := (norm_nonneg s).trans hs
  obtain ⟨hi, he⟩ := iid_shifted_row_energy μ v hX hm hvar s
  have hM : (∫ x : Fin N → 𝕂, ‖s-∑ i, v i*x i‖^2 ∂Measure.pi (fun _ => μ)) ≤ K^2+1 := by
    rw [he]
    have hn : ‖s‖^2 ≤ K^2 := by nlinarith [norm_nonneg s]
    linarith
  exact soft_normalizer_lower (Measure.pi (fun _ : Fin N => μ))
    (fun x => ‖s-∑ i, v i*x i‖^2) (by fun_prop) hi (fun _ => sq_nonneg _) a (K^2+1) ha hM

lemma gaussianFiniteNormalizer_log_deriv (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (hm : (∫ x : 𝕂, x ∂μ) = 0)
    (hvar : (∫ x : 𝕂, ‖x‖^2 ∂μ) = 1)
    (a : ℝ) (ha : 0 < a) (v : Fin N → 𝕂) (hv : ∑ i, ‖v i‖^2 ≤ 1) (s w : 𝕂) :
    deriv (fun t : ℝ => Real.log (gaussianFiniteNormalizer μ a v (s+t • w))) 0 =
      gaussianFiniteDirectional μ a v w s/gaussianFiniteNormalizer μ a v s := by
  have hpos : 0 < gaussianFiniteNormalizer μ a v s :=
    (Real.exp_pos _).trans_le (gaussianFiniteNormalizer_lower μ hX hm hvar a ha v hv s ‖s‖ le_rfl)
  have hd := gaussianFiniteNormalizer_hasDerivAt μ a ha v s w 0
  have hn : gaussianFiniteNormalizer μ a v (s+(0 : ℝ) • w) ≠ 0 := by
    simpa only [zero_smul, add_zero] using ne_of_gt hpos
  simpa only [zero_smul, add_zero] using (hd.log hn).deriv

#print axioms gaussianFiniteNormalizer_hasDerivAt
#print axioms gaussianFiniteNormalizer_lower
#print axioms gaussianFiniteNormalizer_log_deriv
end SpectralRadiusUpperTail

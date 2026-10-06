import SpectralRadiusUpperTail.GaussianLogProductComparison
import SpectralRadiusUpperTail.GaussianNormalizerProducts

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

lemma real_spectralTilt_logNormalizer_error (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℝ, x ∂μ) = 0) (hvar : (∫ x : ℝ, ‖x‖^2 ∂μ) = 1)
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun x : ℝ => Real.exp (c*‖x‖^2)) μ)
    (a : ℝ) (ha : 0 < a) (n : ℕ) (L : ℝ) (hL : 0 ≤ L)
    (v : Fin n → ℝ) (hv : (∑ i, ‖v i‖^2) = 1)
    (hflat : ∀ i, ‖v i‖ ≤ L/Real.sqrt (n : ℝ)) (b : ℝ) :
    |Real.log (∏ i : Fin n, gaussianFiniteNormalizer μ a v (spectralTiltTarget b (zeroExtendVector v) i))-
      (n : ℝ)*(Real.log (Real.sqrt (a/(a+2)))-b^2/(a+2))| ≤
        (n : ℝ)*gaussianNormalizerLogErrorConstant μ standardNormal a (‖b‖*L)*
          (L/Real.sqrt (n : ℝ)) := by
  have hX : MemLp (fun x : ℝ => x) 2 μ :=
    (memLp_two_iff_integrable_sq_norm (by fun_prop)).mpr
      (squareExp_norm_pow_integrable μ c hc hexp 2)
  let t : Fin n → ℝ := spectralTiltTarget b (zeroExtendVector v)
  have hflat' : ∀ i : Fin n, ‖zeroExtendVector v i.val‖ ≤ L/Real.sqrt (n : ℝ) := by
    simpa only [zeroExtendVector_fin] using hflat
  have hG : MemLp (fun x : ℝ => x) 2 standardNormal := by
    convert! (memLp_id_gaussianReal' (μ := 0) (v := 1) (2 : ℝ≥0∞) (by norm_num)) using 1
  have hmG : (∫ x : ℝ, x ∂standardNormal) = 0 := by
    simpa using standardNormal_odd_moment 0
  have hvG : (∫ x : ℝ, ‖x‖^2 ∂standardNormal) = 1 := by
    simpa only [Real.norm_eq_abs,sq_abs] using standardNormal_second_moment
  have hpμ : (∫ x : ℝ, x^2 ∂μ) = 1 := by
    simpa only [Real.norm_eq_abs,sq_abs] using hvar
  have h3G : Integrable (fun x : ℝ => ‖x‖^3) standardNormal := by
    simpa only [norm_pow] using (standardNormal_pow_integrable 3).norm
  have hh := gaussianNormalizer_product_log_comparison_flat μ standardNormal
    hX hG hm hmG hvar hvG (hpμ.trans standardNormal_second_moment.symm)
    (squareExp_norm_pow_integrable μ c hc hexp 3) h3G
    a ha n v hv.le (L/Real.sqrt (n : ℝ)) (by positivity) hflat t (‖b‖*L)
    (fun i => spectralTiltTarget_bound b (zeroExtendVector v) L hflat' i)
  have henergy : (∑ i, (t i)^2) = (n : ℝ)*b^2 := by
    have he := spectralTiltTarget_energy (n := n) b (zeroExtendVector v)
      (by simpa only [zeroExtendVector_fin] using hv)
    simpa only [Real.norm_eq_abs,sq_abs] using he
  have he : Real.log (∏ i : Fin n, gaussianFiniteNormalizer standardNormal a v (t i)) =
      (n : ℝ)*(Real.log (Real.sqrt (a/(a+2)))-b^2/(a+2)) := by
    rw [real_gaussian_normalizer_product_log a ha v hv t,henergy]
    ring
  rw [he] at hh
  exact hh

#print axioms real_spectralTilt_logNormalizer_error
end SpectralRadiusUpperTail

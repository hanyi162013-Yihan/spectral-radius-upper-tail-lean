import SpectralRadiusUpperTail.ComplexWitnessProbability
import SpectralRadiusUpperTail.ComplexUpperRateAlgebra
import SpectralRadiusUpperTail.ENNExponentialRatio

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal

lemma complex_witness_probability_of_annealed (n : ℕ) (hn : 0 < n)
    (u : ℝ) (hu : 0 < u) (z : ℂ) (d L a : ℝ) (P : Measure (Fin n → Fin n → ℂ))
    (hA : (∫⁻ x, fullSpectralSphereWeight n u z x ∂P) ≤ ENNReal.ofReal (Real.exp ((n : ℝ)*a))) :
    P (complexApproximateBulkEvent n u z d L) ≤
      ENNReal.ofReal (Real.exp ((n : ℝ)*(a-(Real.log u-1-d/u-L)))) := by
  have hh := (complex_witness_probability_bound n hn u hu z d L P).trans (mul_le_mul' le_rfl hA)
  rw [ennreal_exp_ratio] at hh
  convert! hh using 1
  congr 1
  ring

lemma complex_fixed_grid_point_bound (n : ℕ) (hn : 0 < n)
    (u r R M ε : ℝ) (hu : 0 < u) (hr : 1 < r) (z : ℂ)
    (hrz : r ≤ ‖z‖) (hzR : ‖z‖ ≤ R) (P : Measure (Fin n → Fin n → ℂ))
    (hA : (∫⁻ x, fullSpectralSphereWeight n u z x ∂P) ≤
      ENNReal.ofReal (Real.exp ((n : ℝ)*(complexAnnealedExponent u ‖z‖+ε)))) :
    P (complexApproximateBulkEvent n u z (u^2) (2*Real.log ‖z‖+2*u*M^2+ε)) ≤
      ENNReal.ofReal (Real.exp ((n : ℝ)*(-rate 2 r+u*(1+R^2+2*M^2)+2*ε))) := by
  apply (complex_witness_probability_of_annealed n hn u hu z (u^2)
    (2*Real.log ‖z‖+2*u*M^2+ε) (complexAnnealedExponent u ‖z‖+ε) P hA).trans
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
  have hs : u^2/u = u := by field_simp
  rw [hs]
  have hh := complex_fixed_grid_rate_bound u r R ‖z‖ M ε hu hr hrz hzR
  linarith

#print axioms complex_witness_probability_of_annealed
#print axioms complex_fixed_grid_point_bound
end SpectralRadiusUpperTail

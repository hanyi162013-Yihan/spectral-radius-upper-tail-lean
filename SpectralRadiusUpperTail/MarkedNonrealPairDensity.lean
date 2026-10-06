import SpectralRadiusUpperTail.MarkedNonrealPairReference
import SpectralRadiusUpperTail.RealPairGaussianComplexMarginal
import SpectralRadiusUpperTail.ComplexUpperHalfPlaneLIntegral
import SpectralRadiusUpperTail.GaussianErfcMeasurable

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal

noncomputable def markedNonrealRawKernel (m : ℕ) (z : ℂ) : ℝ≥0∞ :=
  (ENNReal.ofReal (Real.exp (-‖z‖^2))*
    ENNReal.ofReal (gaussianErfcCorrection (Real.sqrt 2*|z.im|)))*
      ENNReal.ofReal (ginibreExpPartial (m+1) (‖z‖^2))

theorem markedNonrealRawKernel_measurable (m : ℕ) : Measurable (markedNonrealRawKernel m) := by
  have hc : Measurable (fun z : ℂ =>
      ENNReal.ofReal (gaussianErfcCorrection (Real.sqrt 2*|z.im|))) := by
    have he : Measurable (fun z : ℂ => gaussianErfc (Real.sqrt 2*|z.im|)) :=
      gaussianErfc_measurable.comp (by fun_prop)
    unfold gaussianErfcCorrection
    fun_prop
  have hp : Measurable (fun z : ℂ => ENNReal.ofReal (ginibreExpPartial (m+1) (‖z‖^2))) := by
    unfold ginibreExpPartial
    fun_prop
  exact ((by fun_prop : Measurable (fun z : ℂ => ENNReal.ofReal (Real.exp (-‖z‖^2)))).mul hc).mul hp

/-- The remaining pair-block integral is an explicit scalar integral on
the upper half-plane, including the exact erfc correction. -/
theorem markedNonrealPairTestIntegral_eq_density
    (m : ℕ) (g : ℂ → ℝ≥0∞) (hg : Measurable g) :
    markedNonrealPairTestIntegral m g=ENNReal.ofReal (4*Real.pi)*
      ∫⁻ z : ℂ in {z | 0 < z.im}, markedNonrealRawKernel m z*g z := by
  let H := fun p : ℝ × ℝ => ENNReal.ofReal (ginibreExpPartial (m+1) (p.1^2+p.2))*
    g ((p.1 : ℂ)+(Real.sqrt p.2 : ℂ)*Complex.I)
  have hH : Measurable H := by
    have hp : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (ginibreExpPartial (m+1) (p.1^2+p.2))) := by
      unfold ginibreExpPartial
      fun_prop
    exact hp.mul (hg.comp (by fun_prop))
  have h := realPairGaussian_complex_marginal H hH
  change markedNonrealPairTestIntegral m g=_ at h
  rw [h,complex_upperHalfPlane_lintegral (fun z => markedNonrealRawKernel m z*g z)
    ((markedNonrealRawKernel_measurable m).mul hg)]
  congr 1
  apply lintegral_congr
  intro x
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro y hy
  change 0 < y at hy
  dsimp only [H]
  rw [Real.sqrt_sq hy.le]
  have hn : ‖(x : ℂ)+(y : ℂ)*Complex.I‖^2=x^2+y^2 := by
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply]
    ring
  simp only [markedNonrealRawKernel,hn,Complex.add_im,Complex.ofReal_im,
    Complex.mul_im,Complex.ofReal_re,Complex.I_im,Complex.I_re,mul_one,mul_zero,
    add_zero,zero_add,abs_of_pos hy]
  ac_rfl

#print axioms markedNonrealRawKernel_measurable
#print axioms markedNonrealPairTestIntegral_eq_density
end SpectralRadiusUpperTail

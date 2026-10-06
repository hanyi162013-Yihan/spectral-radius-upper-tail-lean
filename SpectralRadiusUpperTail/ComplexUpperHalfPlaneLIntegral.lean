import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal

theorem complex_upperHalfPlane_lintegral (f : ℂ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z : ℂ in {z | 0 < z.im}, f z)=
      ∫⁻ x : ℝ, ∫⁻ y in Set.Ioi (0 : ℝ), f ((x : ℂ)+(y : ℂ)*Complex.I) := by
  have h := Complex.volume_preserving_equiv_real_prod.symm.setLIntegral_comp_preimage_emb
    Complex.measurableEquivRealProd.symm.measurableEmbedding f {z : ℂ | 0 < z.im}
  have hp : Complex.measurableEquivRealProd.symm ⁻¹' {z : ℂ | 0 < z.im}=
      Set.univ ×ˢ Set.Ioi (0 : ℝ) := by
    ext p
    simp
  rw [hp] at h
  rw [← h]
  change (∫⁻ p in Set.univ ×ˢ Set.Ioi (0 : ℝ), f (Complex.measurableEquivRealProd.symm p)
    ∂(volume : Measure ℝ).prod volume)=_
  have hf' : Measurable (fun p : ℝ × ℝ => f (Complex.measurableEquivRealProd.symm p)) :=
    hf.comp Complex.measurableEquivRealProd.symm.measurable
  rw [setLIntegral_prod (fun p : ℝ × ℝ => f (Complex.measurableEquivRealProd.symm p)) hf'.aemeasurable]
  simp only [Measure.restrict_univ]
  have he (p : ℝ × ℝ) : Complex.measurableEquivRealProd.symm p=
      (p.1 : ℂ)+(p.2 : ℂ)*Complex.I := by
    apply Complex.ext <;> simp
  simp_rw [he]

theorem complex_scale_lintegral (c : ℝ) (hc : 0 < c)
    (f : ℂ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z : ℂ, f z)=ENNReal.ofReal (c^2)*∫⁻ z : ℂ, f (c • z) := by
  have hm := Measure.map_addHaar_smul (volume : Measure ℂ) hc.ne'
  have h := congrArg (fun μ : Measure ℂ => ∫⁻ z, f z ∂μ) hm
  rw [lintegral_map hf (by fun_prop),lintegral_smul_measure,smul_eq_mul,
    Complex.finrank_real_complex,abs_inv,abs_of_pos (sq_pos_of_pos hc),ENNReal.ofReal_inv_of_pos
      (sq_pos_of_pos hc)] at h
  rw [h,← mul_assoc,ENNReal.mul_inv_cancel
    (ENNReal.ofReal_pos.mpr (sq_pos_of_pos hc)).ne' ENNReal.ofReal_ne_top,one_mul]

#print axioms complex_upperHalfPlane_lintegral
#print axioms complex_scale_lintegral
end SpectralRadiusUpperTail

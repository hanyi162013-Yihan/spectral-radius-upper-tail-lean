import SpectralRadiusUpperTail.RealSchurNativeGaussianCoordinates

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal

theorem realSchurNativeSpectralMeasure_one_lintegral
    (n : ℝ) (F : ℝ × (ℝ × ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ v, F v ∂realSchurNativeSpectralMeasure 1 n) =
      ∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-(n/2)*x^2))*F (x,0,0) := by
  have hC : Measurable (fun A : (Fin 1 × Fin 1) → ℝ =>
      F (realSchurNativeSpectralCoordinates 1 A)) :=
    hF.comp (realSchurNativeSpectralCoordinates_measurable 1)
  rw [realSchurNativeSpectralMeasure,lintegral_map hF (realSchurNativeSpectralCoordinates_measurable 1),
    realSchurNativeGaussianMeasure,realSchurNativeAtomicEntrySet_one,Measure.restrict_univ,
    realArrayGaussianMeasure,lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hC]
  simp_rw [realSchurNativeSpectralCoordinates_one]
  let : Unique (Fin 1 × Fin 1) :=
    { default := (0,0), uniq := fun _ => Subsingleton.elim _ _ }
  change (∫⁻ A : (Fin 1 × Fin 1) → ℝ,
    ENNReal.ofReal (Real.exp (-(n/2)*∑ i, (A i)^2))*F (A (0,0),0,0))=_
  let E := MeasurableEquiv.piUnique (fun _ : Fin 1 × Fin 1 => ℝ)
  rw [MeasurePreserving.lintegral_map_equiv
    (fun A : (Fin 1 × Fin 1) → ℝ =>
      ENNReal.ofReal (Real.exp (-(n/2)*∑ i, (A i)^2))*F (A (0,0),0,0)) E.symm
      (volume_preserving_piUnique (fun _ : Fin 1 × Fin 1 => ℝ)).symm]
  apply lintegral_congr
  intro x
  simp [E,MeasurableEquiv.piUnique,Equiv.piUnique]

#print axioms realSchurNativeSpectralMeasure_one_lintegral
end SpectralRadiusUpperTail

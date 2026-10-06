import SpectralRadiusUpperTail.RealPairSpectralGapMeasure
import SpectralRadiusUpperTail.RealPairCanonicalObservable
import SpectralRadiusUpperTail.FiniteCoordinateCanonicalization

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal

theorem realPairGapBlockEntries_joint_measurable :
    Measurable (fun v : ℝ × (ℝ × ℝ) => realPairGapBlockEntries v.1 v.2) := by
  apply measurable_pi_lambda
  intro ij
  rcases ij with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;>
    simp only [realPairGapBlockEntries,realSchurBlock,realSchurPairFromCoordinates] <;> fun_prop

theorem realPairCanonicalEntries_measurable : Measurable realPairCanonicalEntries :=
  realPairGapBlockEntries_joint_measurable.comp realPairSpectralGapCoordinates_measurable

theorem realPairProduct_canonical_value {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : (ι → (Fin 2 × Fin 2) → ℝ) → ℝ≥0∞)
    (hInv : ∀ i A, RealPairOrthogonalInvariant (fun B => H (Function.update A i B)))
    (A : ι → (Fin 2 × Fin 2) → ℝ) :
    H A=H (fun i => realPairCanonicalEntries (A i)) := by
  apply finite_coordinate_canonicalization (fun _ => realPairCanonicalEntries) H _ A
  intro B i
  have h := realPairInvariant_canonical_value
    (fun X => H (Function.update B i X)) (hInv i B) (B i)
  simpa only [Function.update_eq_self] using h

/-- Tensorization of the one-block change of variables. No measurable
orthogonal frames are chosen, and the entire joint spectral/gap law is
an actual pushforward of the independent four-entry Gaussian blocks. -/
theorem realPairProduct_spectralGap_lintegral {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : ℝ) (hn : 0 < n)
    (H : (ι → (Fin 2 × Fin 2) → ℝ) → ℝ≥0∞) (hH : Measurable H)
    (hInv : ∀ i A, RealPairOrthogonalInvariant (fun B => H (Function.update A i B))) :
    (∫⁻ A, H A ∂Measure.pi (fun _ : ι => realPairGaussianNonrealMeasure n)) =
      ∫⁻ v : ι → ℝ × (ℝ × ℝ), H (fun i => realPairGapBlockEntries (v i).1 (v i).2)
        ∂Measure.pi (fun _ : ι => realPairSpectralGapMeasure n) := by
  let := realPairGaussianNonrealMeasure_finite n hn
  let := realPairSpectralGapMeasure_finite n hn
  have hmap := Measure.pi_map_pi (μ := fun _ : ι => realPairGaussianNonrealMeasure n)
    (f := fun _ => realPairSpectralGapCoordinates)
    (fun _ => realPairSpectralGapCoordinates_measurable.aemeasurable)
  have hm : Measurable (fun v : ι → ℝ × (ℝ × ℝ) =>
      H (fun i => realPairGapBlockEntries (v i).1 (v i).2)) := by
    apply hH.comp
    exact measurable_pi_lambda _ (fun i =>
      realPairGapBlockEntries_joint_measurable.comp (measurable_pi_apply i))
  simp only [realPairSpectralGapMeasure]
  have ht : Measurable (fun A : ι → (Fin 2 × Fin 2) → ℝ =>
      fun i => realPairSpectralGapCoordinates (A i)) :=
    measurable_pi_lambda _ (fun i =>
      realPairSpectralGapCoordinates_measurable.comp (measurable_pi_apply i))
  rw [← hmap,lintegral_map hm ht]
  exact lintegral_congr (fun A => realPairProduct_canonical_value H hInv A)

#print axioms realPairGapBlockEntries_joint_measurable
#print axioms realPairCanonicalEntries_measurable
#print axioms realPairProduct_canonical_value
#print axioms realPairProduct_spectralGap_lintegral
end SpectralRadiusUpperTail

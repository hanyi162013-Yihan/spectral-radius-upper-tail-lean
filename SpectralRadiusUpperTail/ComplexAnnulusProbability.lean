import SpectralRadiusUpperTail.ComplexAnnulusWitness
import SpectralRadiusUpperTail.ComplexAnnealedWitnessBound

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal BigOperators

lemma complex_annulus_probability_of_annealed (n : ℕ) (hn : 0 < n)
    (u r R M ε : ℝ) (hu : 0 < u) (hr : 1 < r) (S : Finset ℂ)
    (hS : ∀ z ∈ S, r ≤ ‖z‖ ∧ ‖z‖ ≤ R)
    (hcover : ∀ w : ℂ, r ≤ ‖w‖ → ‖w‖ ≤ R → ∃ z ∈ S, ‖w-z‖ < u)
    (P : Measure (Fin n → Fin n → ℂ))
    (hA : ∀ z ∈ S, (∫⁻ x, fullSpectralSphereWeight n u z x ∂P) ≤
      ENNReal.ofReal (Real.exp ((n : ℝ)*(complexAnnealedExponent u ‖z‖+ε)))) :
    P {x | r ≤ (spectralRadius ℂ (normalizedArray x)).toReal ∧
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (normalizedArray x)‖ ≤ R ∧
      ∀ z ∈ S, regularizedResidualLogDet x z (2*u)/(n : ℝ) ≤ 2*Real.log ‖z‖+2*u*M^2+ε} ≤
        (S.card : ℝ≥0∞)*ENNReal.ofReal (Real.exp ((n : ℝ)*(-rate 2 r+u*(1+R^2+2*M^2)+2*ε))) := by
  have hsub := complex_annulus_bulk_subset r R u u S hcover
    (fun z => 2*Real.log ‖z‖+2*u*M^2+ε) n hn
  apply (measure_mono hsub).trans
  apply (measure_biUnion_finset_le S (fun z => complexApproximateBulkEvent n u z (u^2)
    (2*Real.log ‖z‖+2*u*M^2+ε))).trans
  have hh := Finset.sum_le_sum (fun z hz => complex_fixed_grid_point_bound n hn u r R M ε hu hr z
    (hS z hz).1 (hS z hz).2 P (hA z hz))
  simpa only [Finset.sum_const, nsmul_eq_mul] using hh

#print axioms complex_annulus_probability_of_annealed
end SpectralRadiusUpperTail

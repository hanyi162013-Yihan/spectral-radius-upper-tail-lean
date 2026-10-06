import SpectralRadiusUpperTail.ScalarPushforwardMoments
import Mathlib.MeasureTheory.Constructions.Pi

namespace SpectralRadiusUpperTail
open MeasureTheory

noncomputable def complexifiedLaw (μ : Measure ℝ) : Measure ℂ := μ.map Complex.ofReal

instance complexifiedLaw_probability (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (complexifiedLaw μ) := Measure.isProbabilityMeasure_map (by fun_prop)

lemma complexifiedLaw_mean (μ : Measure ℝ) :
    (∫ z : ℂ, z ∂complexifiedLaw μ) = Complex.ofReal (∫ x : ℝ, x ∂μ) := by
  rw [complexifiedLaw,integral_map (f := fun z : ℂ => z) (by fun_prop) (by fun_prop)]
  exact integral_ofReal

lemma complexifiedLaw_energy (μ : Measure ℝ) :
    (∫ z : ℂ, ‖z‖^2 ∂complexifiedLaw μ) = ∫ x : ℝ, ‖x‖^2 ∂μ := by
  rw [complexifiedLaw,integral_map (f := fun z : ℂ => ‖z‖^2) (by fun_prop) (by fun_prop)]
  simp only [Complex.norm_real]

lemma complexifiedLaw_squareExp (μ : Measure ℝ) (c : ℝ)
    (h : Integrable (fun x : ℝ => Real.exp (c*‖x‖^2)) μ) :
    Integrable (fun z : ℂ => Real.exp (c*‖z‖^2)) (complexifiedLaw μ) := by
  apply (integrable_map_measure (g := fun z : ℂ => Real.exp (c*‖z‖^2))
    (by fun_prop) (show AEMeasurable Complex.ofReal μ by fun_prop)).mpr
  simpa only [Function.comp_def,Complex.norm_real] using h

lemma iid_complexifiedLaw {ι : Type*} [Fintype ι] (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (Measure.pi (fun _ : ι => μ)).map (fun x i => (x i : ℂ)) =
      Measure.pi (fun _ : ι => complexifiedLaw μ) :=
  Measure.pi_map_pi (fun _ => by fun_prop)

#print axioms complexifiedLaw
#print axioms complexifiedLaw_probability
#print axioms complexifiedLaw_mean
#print axioms complexifiedLaw_energy
#print axioms complexifiedLaw_squareExp
#print axioms iid_complexifiedLaw
end SpectralRadiusUpperTail

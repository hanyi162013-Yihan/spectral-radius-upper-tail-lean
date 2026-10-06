import SpectralRadiusUpperTail.EuclideanComplexification
import SpectralRadiusUpperTail.ConvexConcentrationInput
import SpectralRadiusUpperTail.RealComplexIidLaw

namespace SpectralRadiusUpperTail
open MeasureTheory Filter WithLp
open scoped Topology NNReal

lemma complexifiedLaw_second_integrable (μ : Measure ℝ)
    (h2 : Integrable (fun x : ℝ => ‖x‖^2) μ) :
    Integrable (fun z : ℂ => ‖z‖^2) (complexifiedLaw μ) := by
  apply (integrable_map_measure (g := fun z : ℂ => ‖z‖^2)
    (by fun_prop) (show AEMeasurable Complex.ofReal μ by fun_prop)).mpr
  simpa only [Function.comp_def, Complex.norm_real] using h2

lemma convex_concentration_complexifiedLaw (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hconv : IidConvexConcentration μ) : IidConvexConcentration (complexifiedLaw μ) := by
  intro L δ hL hδ
  obtain ⟨C, hC, q, hq, ht⟩ := hconv L δ hL hδ
  refine ⟨C, hC, q, hq, ?_⟩
  filter_upwards [ht] with n hn f hfc hf
  have hF := convex_complexification_restrict (n*n) f hfc
  have hLip := lipschitz_complexification_restrict (n*n) f (L/(n : ℝ≥0)) hf
  have hb := hn (fun x => f (euclideanComplexify (n*n) x)) hF hLip
  letI : MeasurableSpace (EuclideanSpace ℂ (Fin (n*n))) := borel _
  letI : BorelSpace (EuclideanSpace ℂ (Fin (n*n))) := ⟨rfl⟩
  have hm : Measurable (fun x : Fin (n*n) → ℂ => f (toLp 2 x)) :=
    hf.continuous.measurable.comp (PiLp.continuous_toLp 2 (fun _ : Fin (n*n) => ℂ)).measurable
  have he := centered_tail_map (Measure.pi (fun _ : Fin (n*n) => μ))
    (Measure.pi (fun _ : Fin (n*n) => complexifiedLaw μ))
    (fun x : Fin (n*n) → ℝ => fun i => (x i : ℂ)) (by fun_prop)
    (iid_complexifiedLaw μ) (fun x => f (toLp 2 x)) hm δ
  apply he.symm.trans_le
  convert! hb using 1

#print axioms complexifiedLaw_second_integrable
#print axioms convex_concentration_complexifiedLaw
end SpectralRadiusUpperTail

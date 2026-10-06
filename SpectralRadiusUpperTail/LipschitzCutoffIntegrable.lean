import SpectralRadiusUpperTail.LipschitzArrayIntegrable
import SpectralRadiusUpperTail.LipschitzTruncationMean

namespace SpectralRadiusUpperTail
open MeasureTheory WithLp
open scoped NNReal
variable {𝕂 : Type*} [RCLike 𝕂]

lemma lipschitz_iid_cutoff_integrable (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (n : ℕ) (hn : 0 < n) (R : ℝ) (L : ℝ≥0)
    (h2 : Integrable (fun x : 𝕂 => ‖x‖^2) μ)
    (f : EuclideanSpace 𝕂 (Fin (n*n)) → ℝ) (hf : LipschitzWith (L/(n : ℝ≥0)) f) :
    Integrable (fun x : Fin (n*n) → 𝕂 => f (toLp 2 (fun i => entryCutoff R (x i))))
      (Measure.pi (fun _ => μ)) := by
  letI : MeasurableSpace (EuclideanSpace 𝕂 (Fin (n*n))) := borel _
  letI : BorelSpace (EuclideanSpace 𝕂 (Fin (n*n))) := ⟨rfl⟩
  have hmlp : Measurable (fun x : Fin (n*n) → 𝕂 => toLp 2 x) :=
    (PiLp.continuous_toLp 2 (fun _ : Fin (n*n) => 𝕂)).measurable
  have hmcut : Measurable (fun x : Fin (n*n) → 𝕂 => fun i => entryCutoff R (x i)) :=
    measurable_pi_lambda _ (fun i => (entryCutoff_measurable R).comp (measurable_pi_apply i))
  have hmf := hf.continuous.measurable.comp hmlp
  have hmd := hmf.sub (hmf.comp hmcut)
  have he := (lipschitz_truncation_mean_bound μ n hn R L h2 f hf).1
  have hdi : Integrable (fun x : Fin (n*n) → 𝕂 =>
      f (toLp 2 x)-f (toLp 2 (fun i => entryCutoff R (x i)))) (Measure.pi (fun _ => μ)) := by
    apply (integrable_norm_iff hmd.aestronglyMeasurable).mp
    simpa only [Real.norm_eq_abs, Pi.sub_apply, Function.comp_apply] using! he
  have hi := (lipschitz_iid_array_integrable μ (n*n) h2 _ f hf).sub hdi
  convert! hi using 1
  funext x
  simp

#print axioms lipschitz_iid_cutoff_integrable
end SpectralRadiusUpperTail

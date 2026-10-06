import SpectralRadiusUpperTail.PlanarRadialExteriorIntegral
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Set Metric

/-- Radial integrability with the polar Jacobian implies integrability of
the corresponding function on a complex exterior region. -/
theorem planarRadialExteriorIntegrable (g : ℝ → ℝ) (r : ℝ)
    (hr : 0 < r)
    (hg : IntegrableOn (fun s : ℝ => s*g s) (Ioi r)) :
    IntegrableOn (fun z : ℂ => g ‖z‖) {z | r < ‖z‖} := by
  let f : ℝ → ℝ := (Ioi r).indicator g
  have hglobal : Integrable ((Ioi r).indicator (fun s : ℝ => s*g s)) :=
    (integrable_indicator_iff measurableSet_Ioi).mpr hg
  have hrad : IntegrableOn (fun s : ℝ => s*f s) (Ioi 0) := by
    apply hglobal.integrableOn.congr_fun _ measurableSet_Ioi
    intro s hs
    by_cases hsr : r < s <;> simp [f, Set.indicator, hsr]
  have hwhole : Integrable (fun z : ℂ => f ‖z‖) := by
    apply (integrable_fun_norm_addHaar (μ := (volume : Measure ℂ))).mpr
    simpa only [Complex.finrank_real_complex, Nat.reduceSubDiff,
      pow_one, smul_eq_mul] using hrad
  have hset : MeasurableSet {z : ℂ | r < ‖z‖} :=
    measurableSet_lt measurable_const measurable_norm
  apply hwhole.integrableOn.congr_fun _ hset
  intro z hz
  have hz' : r < ‖z‖ := hz
  simp [f, Set.indicator, hz']

#print axioms planarRadialExteriorIntegrable
end SpectralRadiusUpperTail

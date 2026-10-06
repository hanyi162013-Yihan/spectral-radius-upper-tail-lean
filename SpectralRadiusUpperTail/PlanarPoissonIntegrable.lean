import SpectralRadiusUpperTail.PlanarRadialPoissonIdentity
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Set Metric

theorem planarPoisson_integrableOn (n : ℕ) (r : ℝ)
    (hr : 1 < r) (hnpos : 0 < n)
    (hn : 1/r ≤ (n : ℝ)*(r-1/r)) :
    IntegrableOn (fun z : ℂ => Real.exp (-(n : ℝ)*rate 2 ‖z‖))
      {z | r < ‖z‖} := by
  let f : ℝ → ℝ := (Ioi r).indicator
    (fun s => Real.exp (-(n : ℝ)*rate 2 s))
  have hrad := realGinibreRadial_integrableOn n r hr hn hnpos
  have hset : Ioi r ∩ Ioi (0 : ℝ) = Ioi r := by
    ext s
    constructor
    · exact fun h => h.1
    · exact fun h => ⟨h, lt_trans (by linarith : 0 < r) h⟩
  have hrad' : IntegrableOn
      ((Ioi r).indicator (fun s : ℝ => s * Real.exp (-(n : ℝ)*rate 2 s)))
      (Ioi (0 : ℝ)) := by
    rw [integrableOn_indicator_iff measurableSet_Ioi, hset]
    exact hrad
  have hradEq : (fun s : ℝ => s * f s) =
      (Ioi r).indicator (fun s => s * Real.exp (-(n : ℝ)*rate 2 s)) := by
    funext s
    by_cases hs : r < s <;> simp [f, Set.indicator, hs]
  have hrad'' : IntegrableOn
      (fun s : ℝ => s ^ (Module.finrank ℝ ℂ-1) • f s)
      (Ioi (0 : ℝ)) := by
    simpa only [Complex.finrank_real_complex, Nat.reduceSubDiff, pow_one,
      smul_eq_mul, hradEq] using hrad'
  have hplan : Integrable (fun z : ℂ => f ‖z‖) :=
    (integrable_fun_norm_addHaar (μ := (volume : Measure ℂ))).2 hrad''
  have hE : MeasurableSet {z : ℂ | r < ‖z‖} :=
    measurableSet_lt measurable_const measurable_norm
  have heq : (fun z : ℂ => f ‖z‖) =
      {z : ℂ | r < ‖z‖}.indicator
        (fun z => Real.exp (-(n : ℝ)*rate 2 ‖z‖)) := by
    funext z
    by_cases hz : r < ‖z‖ <;> simp [f, Set.indicator, hz]
  rw [heq] at hplan
  exact (integrable_indicator_iff hE).mp hplan

#print axioms planarPoisson_integrableOn
end SpectralRadiusUpperTail

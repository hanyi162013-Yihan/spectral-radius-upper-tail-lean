import SpectralRadiusUpperTail.RealGinibreNonrealCoreCompare
import SpectralRadiusUpperTail.RealGinibreWeightedRadialCore
import SpectralRadiusUpperTail.PlanarRadialExteriorIntegrable
import SpectralRadiusUpperTail.ExponentialPrefactorBudget
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Set Metric Filter
open scoped Topology

/-- After one polar Jacobian, the nonreal weighted one-point term is bounded
by the same shifted-Gamma envelope, at power `k+1`. -/
theorem realGinibreNonrealDensityAt_weighted_upper_of_budget
    (n k : ℕ) (hn : 1 ≤ n) (ε : ℝ)
    (hbudget : Real.log (n : ℝ)-
        Real.log (realGinibreCoreDensity n 1)+1/2 ≤ (n : ℝ)*ε) :
    (∫ z : ℂ in {z | 1 < ‖z‖},
      ‖z‖^(2*k)*realGinibreNonrealDensityAt n z) ≤
      (2*(volume : Measure ℂ).real (ball 0 1)) *
        Real.exp ((n : ℝ)*ε) *
          Real.exp (realGinibreWeightedUpperExponent n (k+1)) := by
  let M : ℝ := Real.exp ((n : ℝ)*ε)
  let C : ℝ := 2*(volume : Measure ℂ).real (ball 0 1)
  let g : ℝ → ℝ := fun s => M*(s^(2*k)*realGinibreCoreDensity n s)
  have hnpos : 0 < n := by omega
  have hM : 0 ≤ M := (Real.exp_pos _).le
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hrad0 := realGinibre_radialCore_integrableOn n k hnpos
  have hconst : IntegrableOn
      (fun s : ℝ => M*(s*(s^(2*k)*realGinibreCoreDensity n s)))
      (Ioi 1) := hrad0.const_mul M
  have hrad : IntegrableOn (fun s : ℝ => s*g s) (Ioi 1) := by
    apply hconst.congr_fun _ measurableSet_Ioi
    intro s hs
    dsimp [g]
    ring
  have henv : IntegrableOn (fun z : ℂ => g ‖z‖)
      {z | 1 < ‖z‖} :=
    planarRadialExteriorIntegrable g 1 (by norm_num) hrad
  have hset : MeasurableSet {z : ℂ | 1 < ‖z‖} :=
    measurableSet_lt measurable_const measurable_norm
  have hmeas : Measurable (fun z : ℂ =>
      ‖z‖^(2*k)*realGinibreNonrealDensityAt n z) :=
    (measurable_norm.pow_const _).mul
      (realGinibreNonrealDensityAt_measurable n)
  have hpoint (z : ℂ) (hz : 1 ≤ ‖z‖) :
      ‖z‖^(2*k)*realGinibreNonrealDensityAt n z ≤ g ‖z‖ := by
    have hp : 0 ≤ ‖z‖^(2*k) := pow_nonneg (norm_nonneg _) _
    have hle := mul_le_mul_of_nonneg_left
      (realGinibreNonrealDensityAt_le_exp_core_of_budget
        n hn ε hbudget z hz) hp
    calc
      _ ≤ ‖z‖^(2*k)*(Real.exp ((n : ℝ)*ε)*
          realGinibreCoreDensity n ‖z‖) := hle
      _ = _ := by dsimp [g, M]; ring
  have hactual : IntegrableOn (fun z : ℂ =>
      ‖z‖^(2*k)*realGinibreNonrealDensityAt n z)
      {z | 1 < ‖z‖} := by
    apply henv.mono' hmeas.aestronglyMeasurable
    filter_upwards [ae_restrict_mem hset] with z hz
    have hz1 : 1 ≤ ‖z‖ := le_of_lt hz
    have hleft : 0 ≤ ‖z‖^(2*k)*realGinibreNonrealDensityAt n z :=
      mul_nonneg (pow_nonneg (norm_nonneg _) _)
        (realGinibreNonrealDensityAt_bound n z hz1).1
    have hright : 0 ≤ g ‖z‖ := by
      dsimp [g]
      exact mul_nonneg hM (mul_nonneg
        (pow_nonneg (norm_nonneg _) _)
        (realGinibreCoreDensity_pos n hnpos ‖z‖ (by linarith)).le)
    simpa only [Real.norm_eq_abs, abs_of_nonneg hleft,
      abs_of_nonneg hright] using hpoint z hz1
  have hmono := setIntegral_mono_on hactual henv hset
    (fun z hz => hpoint z (le_of_lt hz))
  have hpolar := planarRadialExteriorIntegral g 1 (by norm_num)
  have hradEq : (∫ s : ℝ in Ioi 1, s*g s) =
      M*(∫ s : ℝ in Ioi 1,
        s*(s^(2*k)*realGinibreCoreDensity n s)) := by
    calc
      _ = ∫ s : ℝ in Ioi 1,
          M*(s*(s^(2*k)*realGinibreCoreDensity n s)) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro s hs
        dsimp [g]
        ring
      _ = _ := by rw [integral_const_mul]
  calc
    _ ≤ C*(∫ s : ℝ in Ioi 1, s*g s) := by
      simpa only [C] using hmono.trans_eq hpolar
    _ = C*(M*(∫ s : ℝ in Ioi 1,
        s*(s^(2*k)*realGinibreCoreDensity n s))) := by rw [hradEq]
    _ ≤ C*(M*Real.exp (realGinibreWeightedUpperExponent n (k+1))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (realGinibre_radialCore_integral_upper n k hnpos) hM) hC
    _ = _ := by dsimp [C, M]; ring

#print axioms realGinibreNonrealDensityAt_weighted_upper_of_budget
end SpectralRadiusUpperTail

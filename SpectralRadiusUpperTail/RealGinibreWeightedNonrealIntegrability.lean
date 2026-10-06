import SpectralRadiusUpperTail.RealGinibreWeightedNonrealUpper

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal

theorem realGinibreNonrealDensityAt_weighted_integrableOn
    (n k : ℕ) (hn : 0 < n) :
    IntegrableOn (fun z : ℂ => ‖z‖^(2*k)*realGinibreNonrealDensityAt n z)
      {z | 1 < ‖z‖} := by
  let ε : ℝ := (Real.log (n : ℝ)-Real.log (realGinibreCoreDensity n 1)+1/2)/(n : ℝ)
  let M : ℝ := Real.exp ((n : ℝ)*ε)
  let g : ℝ → ℝ := fun s => M*(s^(2*k)*realGinibreCoreDensity n s)
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hbudget : Real.log (n : ℝ)-Real.log (realGinibreCoreDensity n 1)+1/2 ≤ (n : ℝ)*ε := by
    dsimp [ε]
    rw [mul_div_cancel₀ _ hnR]
  have hconst : IntegrableOn
      (fun s : ℝ => M*(s*(s^(2*k)*realGinibreCoreDensity n s))) (Set.Ioi 1) :=
    (realGinibre_radialCore_integrableOn n k hn).const_mul M
  have hrad : IntegrableOn (fun s : ℝ => s*g s) (Set.Ioi 1) := by
    apply hconst.congr_fun _ measurableSet_Ioi
    intro s hs
    dsimp [g]
    ring
  have henv : IntegrableOn (fun z : ℂ => g ‖z‖) {z | 1 < ‖z‖} :=
    planarRadialExteriorIntegrable g 1 (by norm_num) hrad
  have hm : Measurable (fun z : ℂ => ‖z‖^(2*k)*realGinibreNonrealDensityAt n z) :=
    (measurable_norm.pow_const _).mul (realGinibreNonrealDensityAt_measurable n)
  apply henv.mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem (measurableSet_lt measurable_const measurable_norm)] with z hz
  have hpos : 0 ≤ ‖z‖^(2*k)*realGinibreNonrealDensityAt n z :=
    mul_nonneg (pow_nonneg (norm_nonneg _) _) (realGinibreNonrealDensityAt_bound n z hz.le).1
  rw [Real.norm_eq_abs,abs_of_nonneg hpos]
  have hb := realGinibreNonrealDensityAt_le_exp_core_of_budget n (by omega) ε hbudget z hz.le
  calc
    _ ≤ ‖z‖^(2*k)*(M*realGinibreCoreDensity n ‖z‖) :=
      mul_le_mul_of_nonneg_left hb (pow_nonneg (norm_nonneg _) _)
    _ = g ‖z‖ := by dsimp [g]; ring

theorem realGinibreNonrealDensityAt_weighted_lintegral
    (n k : ℕ) (hn : 0 < n) :
    (∫⁻ z : ℂ in {z | 1 < ‖z‖},
      ENNReal.ofReal (‖z‖^(2*k)*realGinibreNonrealDensityAt n z)) =
      ENNReal.ofReal (∫ z : ℂ in {z | 1 < ‖z‖},
        ‖z‖^(2*k)*realGinibreNonrealDensityAt n z) := by
  apply (ofReal_integral_eq_lintegral_ofReal
    (realGinibreNonrealDensityAt_weighted_integrableOn n k hn) _).symm
  filter_upwards [ae_restrict_mem (measurableSet_lt measurable_const measurable_norm)] with z hz
  exact mul_nonneg (pow_nonneg (norm_nonneg _) _) (realGinibreNonrealDensityAt_bound n z hz.le).1

#print axioms realGinibreNonrealDensityAt_weighted_integrableOn
#print axioms realGinibreNonrealDensityAt_weighted_lintegral
end SpectralRadiusUpperTail

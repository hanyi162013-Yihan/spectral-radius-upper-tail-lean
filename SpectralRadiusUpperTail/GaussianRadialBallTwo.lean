import SpectralRadiusUpperTail.GaussianRadialCumulative
import SpectralRadiusUpperTail.GaussianNormIntegrable

namespace SpectralRadiusUpperTail
open MeasureTheory Metric
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

lemma gaussian_integral_two (μ : Measure E) [μ.IsAddHaarMeasure]
    (hdim : Module.finrank ℝ E = 2) (c : ℝ) (hc : 0 < c) :
    (∫ x, Real.exp (-c*‖x‖^2) ∂μ) = μ.real (ball 0 1)/c := by
  have he := integral_fun_norm_addHaar μ (fun r : ℝ => Real.exp (-c*r^2))
  simp only [hdim,show (2 : ℕ)-1 = 1 by norm_num,pow_one,smul_eq_mul,nsmul_eq_mul] at he
  rw [gaussian_radial_integral_Ioi c hc] at he
  rw [he]
  field_simp
  <;> ring

lemma gaussian_integral_ball_two (μ : Measure E) [μ.IsAddHaarMeasure]
    (hdim : Module.finrank ℝ E = 2) (c R : ℝ) (hc : 0 < c) (hR : 0 ≤ R) :
    (∫ x in ball 0 R, Real.exp (-c*‖x‖^2) ∂μ) =
      μ.real (ball 0 1)/c*(1-Real.exp (-c*R^2)) := by
  have he := integral_fun_norm_addHaar μ
    ((Set.Iio R).indicator (fun r : ℝ => Real.exp (-c*r^2)))
  have hl : (fun x : E => (Set.Iio R).indicator (fun r : ℝ => Real.exp (-c*r^2)) ‖x‖) =
      (ball (0 : E) R).indicator (fun x : E => Real.exp (-c*‖x‖^2)) := by
    funext x
    simp only [Set.indicator,Set.mem_Iio,mem_ball,dist_zero_right]
  rw [hl,integral_indicator measurableSet_ball] at he
  simp only [hdim,show (2 : ℕ)-1 = 1 by norm_num,pow_one,smul_eq_mul,nsmul_eq_mul] at he
  have hr : (∫ r : ℝ in Set.Ioi 0, r*(Set.Iio R).indicator (fun y : ℝ => Real.exp (-c*y^2)) r) =
      ∫ r : ℝ in Set.Ioo 0 R, r*Real.exp (-c*r^2) := by
    have hf : (fun r : ℝ => r*(Set.Iio R).indicator (fun y : ℝ => Real.exp (-c*y^2)) r) =
        (Set.Iio R).indicator (fun r : ℝ => r*Real.exp (-c*r^2)) := by
      funext r
      by_cases h : r < R <;> simp [Set.indicator,h]
    rw [hf,integral_indicator measurableSet_Iio,Measure.restrict_restrict measurableSet_Iio]
    rw [show Set.Iio R ∩ Set.Ioi (0 : ℝ) = Set.Ioo 0 R by
      ext r
      simp only [Set.mem_inter_iff,Set.mem_Iio,Set.mem_Ioi,Set.mem_Ioo]
      exact and_comm]
  rw [hr,gaussian_radial_integral_Ioo c R hc hR] at he
  rw [he]
  ring

#print axioms gaussian_integral_two
#print axioms gaussian_integral_ball_two
end SpectralRadiusUpperTail

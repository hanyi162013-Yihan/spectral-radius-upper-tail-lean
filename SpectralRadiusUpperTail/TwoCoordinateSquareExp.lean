import SpectralRadiusUpperTail.MgfSquareMoment
import Mathlib.Analysis.RCLike.Basic

namespace SpectralRadiusUpperTail
open MeasureTheory

lemma exp_half_sum_le (a b : ℝ) :
    Real.exp ((a+b)/2) ≤ (Real.exp a+Real.exp b)/2 := by
  have ha : (Real.exp (a/2))^2 = Real.exp a := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hb : (Real.exp (b/2))^2 = Real.exp b := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hab : Real.exp (a/2)*Real.exp (b/2) = Real.exp ((a+b)/2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  nlinarith [sq_nonneg (Real.exp (a/2)-Real.exp (b/2))]

/-- Coordinate square-exponential bounds control the norm, without independence
between the two coordinates. This includes the real field, with zero imaginary part. -/
theorem two_coordinate_squareExp {Ω 𝕂 : Type*} [MeasurableSpace Ω] [RCLike 𝕂]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → 𝕂)
    (hU : AEStronglyMeasurable U μ) (c : ℝ)
    (hre : Integrable (fun x => Real.exp (c*(RCLike.re (U x))^2)) μ)
    (him : Integrable (fun x => Real.exp (c*(RCLike.im (U x))^2)) μ)
    (hreb : (∫ x, Real.exp (c*(RCLike.re (U x))^2) ∂μ) ≤ 2)
    (himb : (∫ x, Real.exp (c*(RCLike.im (U x))^2) ∂μ) ≤ 2) :
    Integrable (fun x => Real.exp ((c/2)*‖U x‖^2)) μ ∧
      (∫ x, Real.exp ((c/2)*‖U x‖^2) ∂μ) ≤ 2 := by
  have hp (x : Ω) : Real.exp ((c/2)*‖U x‖^2) ≤
      (Real.exp (c*(RCLike.re (U x))^2)+Real.exp (c*(RCLike.im (U x))^2))/2 := by
    convert exp_half_sum_le (c*(RCLike.re (U x))^2) (c*(RCLike.im (U x))^2) using 1
    rw [RCLike.norm_sq_eq_def]
    ring
  have hmeas : AEStronglyMeasurable (fun x => Real.exp ((c/2)*‖U x‖^2)) μ :=
    Real.continuous_exp.comp_aestronglyMeasurable ((hU.norm.pow 2).const_mul (c/2))
  have htop : Integrable (fun x =>
      (Real.exp (c*(RCLike.re (U x))^2)+Real.exp (c*(RCLike.im (U x))^2))/2) μ :=
    (hre.add him).div_const 2
  have hi := htop.mono_nonneg hmeas
    (Filter.Eventually.of_forall (fun _ => Real.exp_nonneg _)) (Filter.Eventually.of_forall hp)
  refine ⟨hi, ?_⟩
  have h := integral_mono hi htop hp
  rw [integral_div, integral_add hre him] at h
  linarith

#print axioms two_coordinate_squareExp
end SpectralRadiusUpperTail

import SpectralRadiusUpperTail.TalagrandExponentialInterpolation
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory

/-- Uniformly bounded measurable energies have integrable exponential
under every probability law. -/
theorem integrable_exp_of_bounded_energy
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (e : Ω → ℝ) (he : Measurable e)
    (C : ℝ) (hC : ∀ x, e x ≤ C) :
    Integrable (fun x => Real.exp (e x)) μ := by
  apply (integrable_const (Real.exp C)).mono'
    (Real.measurable_exp.comp he).aestronglyMeasurable
  filter_upwards [] with x
  change |Real.exp (e x)| ≤ Real.exp C
  rw [abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (hC x)

/-- The Hölder product is also integrable when both input energies have a
common upper bound and the interpolation weight lies in `[0,1]`. -/
theorem integrable_exp_geometric_mix
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (f g : Ω → ℝ) (hf : Measurable f) (hg : Measurable g)
    (C θ : ℝ) (hfC : ∀ x, f x ≤ C) (hgC : ∀ x, g x ≤ C)
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    Integrable (fun x => (Real.exp (f x))^θ *
      (Real.exp (g x))^(1-θ)) μ := by
  have heq (x : Ω) :
      (Real.exp (f x))^θ * (Real.exp (g x))^(1-θ) =
        Real.exp (θ*f x+(1-θ)*g x) := by
    rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
    congr 1
    ring
  have hbound (x : Ω) : θ*f x+(1-θ)*g x ≤ C := by
    have h1 := mul_le_mul_of_nonneg_left (hfC x) hθ
    have h2 := mul_le_mul_of_nonneg_left (hgC x) (by linarith : 0 ≤ 1-θ)
    nlinarith
  have hi : Integrable
      (fun x => Real.exp (θ*f x+(1-θ)*g x)) μ :=
    integrable_exp_of_bounded_energy μ _
      (by fun_prop) C hbound
  simpa only [← heq] using hi

#print axioms integrable_exp_of_bounded_energy
#print axioms integrable_exp_geometric_mix
end SpectralRadiusUpperTail

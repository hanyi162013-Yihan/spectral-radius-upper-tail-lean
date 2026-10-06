import SpectralRadiusUpperTail.TalagrandRealWeightedHolder
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory

/-- Integrate a pointwise convex energy interpolation using weighted
Hölder. The additive error becomes one scalar exponential factor. -/
theorem integral_exp_interpolation_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (d f g : Ω → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hdInt : Integrable (fun x => Real.exp (d x)) μ)
    (hfInt : Integrable (fun x => Real.exp (f x)) μ)
    (hgInt : Integrable (fun x => Real.exp (g x)) μ)
    (θ c : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hmixInt : Integrable
      (fun x => (Real.exp (f x))^θ*(Real.exp (g x))^(1-θ)) μ)
    (hpoint : ∀ x, d x ≤ θ*f x+(1-θ)*g x+c) :
    (∫ x, Real.exp (d x) ∂μ) ≤
      Real.exp c*(∫ x, Real.exp (f x) ∂μ)^θ*
        (∫ x, Real.exp (g x) ∂μ)^(1-θ) := by
  let h := fun x => (Real.exp (f x))^θ*(Real.exp (g x))^(1-θ)
  have hpointExp (x : Ω) : Real.exp (d x) ≤ Real.exp c*h x := by
    calc
      Real.exp (d x) ≤ Real.exp (θ*f x+(1-θ)*g x+c) :=
        Real.exp_le_exp.mpr (hpoint x)
      _ = Real.exp c*h x := by
        dsimp [h]
        rw [Real.exp_add, Real.exp_add, mul_comm θ (f x),
          mul_comm (1-θ) (g x), Real.exp_mul, Real.exp_mul]
        ring
  have hholder := integral_geometric_mean_le μ
    (fun x => Real.exp (f x)) (fun x => Real.exp (g x))
    (Real.measurable_exp.comp hf) (Real.measurable_exp.comp hg)
    hfInt hgInt θ hθ hθ1
    (fun x => (Real.exp_pos _).le) (fun x => (Real.exp_pos _).le) hmixInt
  calc
    (∫ x, Real.exp (d x) ∂μ) ≤
        ∫ x, Real.exp c*h x ∂μ :=
      integral_mono hdInt (hmixInt.const_mul _) hpointExp
    _ = Real.exp c * ∫ x, h x ∂μ := by rw [integral_const_mul]
    _ ≤ Real.exp c * ((∫ x, Real.exp (f x) ∂μ)^θ *
        (∫ x, Real.exp (g x) ∂μ)^(1-θ)) :=
      mul_le_mul_of_nonneg_left hholder (Real.exp_pos c).le
    _ = _ := by ring

#print axioms integral_exp_interpolation_le
end SpectralRadiusUpperTail

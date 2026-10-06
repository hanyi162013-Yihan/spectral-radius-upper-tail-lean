import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory

/-- Oppositely ordered observables have nonpositive covariance. Integrating
one variable at a time avoids any independence or product-integrability input. -/
lemma opposite_order_integral_mul_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f w : Ω → ℝ)
    (hf : Integrable f μ) (hw : Integrable w μ)
    (hfw : Integrable (fun x => f x*w x) μ)
    (hopp : ∀ x y, (f x-f y)*(w x-w y) ≤ 0) :
    (∫ x, f x*w x ∂μ) ≤ (∫ x, f x ∂μ)*(∫ x, w x ∂μ) := by
  have hp (x : Ω) : f x*w x+(∫ y, f y*w y ∂μ)-f x*(∫ y, w y ∂μ)-
      (∫ y, f y ∂μ)*w x ≤ 0 := by
    have hh : (∫ y, f x*w x+f y*w y-f x*w y-f y*w x ∂μ) ≤ 0 := by
      apply integral_nonpos
      intro y
      change f x*w x+f y*w y-f x*w y-f y*w x ≤ 0
      nlinarith only [hopp x y]
    have hA : Integrable (fun y => f x*w x+f y*w y) μ := (integrable_const _).add hfw
    have hB : Integrable (fun y => f x*w x+f y*w y-f x*w y) μ := hA.sub (hw.const_mul _)
    rw [integral_sub hB (hf.mul_const (w x)),
      integral_sub hA (hw.const_mul (f x)),
      integral_add (integrable_const (f x*w x)) hfw, integral_const_mul, integral_mul_const] at hh
    simpa [integral_const_mul, integral_mul_const] using hh
  have hh := integral_nonpos (μ := μ) hp
  have hA : Integrable (fun x => f x*w x+(∫ y, f y*w y ∂μ)) μ := hfw.add (integrable_const _)
  have hB : Integrable (fun x => f x*w x+(∫ y, f y*w y ∂μ)-f x*(∫ y, w y ∂μ)) μ :=
    hA.sub (hf.mul_const _)
  rw [integral_sub hB (hw.const_mul (∫ y, f y ∂μ)),
    integral_sub hA (hf.mul_const (∫ y, w y ∂μ)),
    integral_add hfw (integrable_const (∫ y, f y*w y ∂μ)), integral_mul_const, integral_const_mul] at hh
  simp [integral_const_mul, integral_mul_const] at hh
  nlinarith

lemma decreasing_weight_mean_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (w : ℝ → ℝ) (hx : Integrable (fun x : ℝ => x) μ) (hw : Integrable w μ)
    (hxw : Integrable (fun x : ℝ => x*w x) μ) (hanti : Antitone w)
    (hwpos : 0 < ∫ x, w x ∂μ) :
    (∫ x : ℝ, x*w x ∂μ)/(∫ x, w x ∂μ) ≤ ∫ x : ℝ, x ∂μ := by
  apply (div_le_iff₀ hwpos).mpr
  apply opposite_order_integral_mul_le μ id w hx hw hxw
  intro x y
  rcases le_total x y with h | h
  · exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h) (sub_nonneg.mpr (hanti h))
  · exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr h) (sub_nonpos.mpr (hanti h))

#print axioms opposite_order_integral_mul_le
#print axioms decreasing_weight_mean_le
end SpectralRadiusUpperTail

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! A genuine probability-integral input to the complex spherical upper bound.
The hypothesis is the entry/row Laplace transform bound, not a matrix tail bound. -/
namespace SpectralRadiusUpperTail
open MeasureTheory

lemma scalar_soft_square (x t u a : ℝ) (ha : 0 < a) :
    -((x-t)^2)/a ≤ 2*u*(x-t)+a*u^2 := by
  apply (div_le_iff₀ ha).2
  nlinarith [sq_nonneg (x-t+a*u)]

lemma planar_soft_square (x y t q u v a : ℝ) (ha : 0 < a) :
    -((x-t)^2+(y-q)^2)/a ≤ 2*(u*x+v*y)-2*(u*t+v*q)+a*(u^2+v^2) := by
  have h₁ := scalar_soft_square x t u a ha
  have h₂ := scalar_soft_square y q v a ha
  rw [neg_add, add_div]
  linarith

/-- The prefactor-free sharp Chernoff bound for a planar row law. -/
theorem planar_soft_integral_le
    (μ : Measure (ℝ × ℝ)) (a s t q : ℝ) (ha : 0 < a) (hs : 0 ≤ s)
    (hint : ∀ u v : ℝ, Integrable (fun x : ℝ × ℝ =>
      Real.exp (2*(u*x.1+v*x.2))) μ)
    (hmgf : ∀ u v : ℝ, (∫ x : ℝ × ℝ, Real.exp (2*(u*x.1+v*x.2)) ∂μ)
      ≤ Real.exp (s*(u^2+v^2))) :
    (∫ x : ℝ × ℝ, Real.exp (-((x.1-t)^2+(x.2-q)^2)/a) ∂μ)
      ≤ Real.exp (-(t^2+q^2)/(a+s)) := by
  let u := t/(a+s)
  let v := q/(a+s)
  let c := -2*(u*t+v*q)+a*(u^2+v^2)
  have hsum : 0 < a+s := by linarith
  have hpoint (x : ℝ × ℝ) :
      Real.exp (-((x.1-t)^2+(x.2-q)^2)/a) ≤
        Real.exp c * Real.exp (2*(u*x.1+v*x.2)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    dsimp [c]
    have h := planar_soft_square x.1 x.2 t q u v a ha
    linarith
  calc
    (∫ x : ℝ × ℝ, Real.exp (-((x.1-t)^2+(x.2-q)^2)/a) ∂μ)
        ≤ ∫ x : ℝ × ℝ, Real.exp c * Real.exp (2*(u*x.1+v*x.2)) ∂μ :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le))
        ((hint u v).const_mul _) (Filter.Eventually.of_forall hpoint)
    _ = Real.exp c * (∫ x : ℝ × ℝ, Real.exp (2*(u*x.1+v*x.2)) ∂μ) :=
      integral_const_mul _ _
    _ ≤ Real.exp c * Real.exp (s*(u^2+v^2)) :=
      mul_le_mul_of_nonneg_left (hmgf u v) (Real.exp_pos _).le
    _ = Real.exp (-(t^2+q^2)/(a+s)) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [c, u, v]
      field_simp [ne_of_gt hsum]
      <;> ring

#print axioms planar_soft_integral_le
end SpectralRadiusUpperTail

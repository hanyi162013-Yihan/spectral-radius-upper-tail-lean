import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

lemma talagrand_exp_curve_antitone :
    Antitone (fun x : ℝ => Real.exp (-x)+Real.exp (x-x^2)) := by
  apply antitone_of_hasDerivAt_nonpos
    (f' := fun x => -Real.exp (-x)+(1-2*x)*Real.exp (x-x^2))
  · intro x
    convert! ((hasDerivAt_id x).neg.exp).add
      (((hasDerivAt_id x).sub ((hasDerivAt_id x).pow 2)).exp) using 1 <;> simp only [Pi.sub_apply, Pi.neg_apply, Pi.pow_apply, id_eq] <;> ring
  · intro x
    change -Real.exp (-x)+(1-2*x)*Real.exp (x-x^2) ≤ 0
    have hbase : 1-2*x ≤ Real.exp (-2*x) := by
      have hh := Real.add_one_le_exp (-2*x)
      linarith
    have hh := mul_le_mul_of_nonneg_right hbase (Real.exp_pos (x-x^2)).le
    rw [← Real.exp_add] at hh
    have he : Real.exp (-2*x+(x-x^2)) ≤ Real.exp (-x) :=
      Real.exp_le_exp.mpr (by nlinarith [sq_nonneg x])
    linarith

lemma talagrand_exp_curve_bound (x : ℝ) (hx : 0 ≤ x) :
    Real.exp (-x)+Real.exp (x-x^2) ≤ 2 := by
  have hh := talagrand_exp_curve_antitone hx
  norm_num at hh
  exact hh

/-- The scalar optimization used in the product induction for Talagrand's
convex-distance inequality. The chosen interpolation weight lies in [0,1]. -/
lemma talagrand_scalar_mixing (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧
      Real.exp (-θ*Real.log a+(1-θ)^2/4) ≤ 2-a := by
  let x := -Real.log a
  have hx : 0 ≤ x := neg_nonneg.mpr (Real.log_nonpos ha.le ha1)
  have he : Real.exp (-x)=a := by dsimp [x]; rw [neg_neg, Real.exp_log ha]
  by_cases hsmall : x ≤ 1/2
  · refine ⟨1-2*x, by linarith, by linarith, ?_⟩
    have harg : -(1-2*x)*Real.log a+(1-(1-2*x))^2/4 = x-x^2 := by
      dsimp [x]
      ring
    rw [harg]
    have hh := talagrand_exp_curve_bound x hx
    rw [he] at hh
    linarith
  · refine ⟨0, le_rfl, by norm_num, ?_⟩
    have hh := talagrand_exp_curve_bound (1/2) (by norm_num)
    have he' : a ≤ Real.exp (-(1/2 : ℝ)) := by
      rw [← he]
      exact Real.exp_le_exp.mpr (by linarith)
    norm_num at hh ⊢
    linarith

lemma talagrand_scalar_average_budget (a : ℝ) (ha : 0 < a) :
    2-a ≤ 1/a := by
  apply (le_div_iff₀ ha).mpr
  nlinarith [sq_nonneg (1-a)]

#print axioms talagrand_exp_curve_antitone
#print axioms talagrand_exp_curve_bound
#print axioms talagrand_scalar_mixing
#print axioms talagrand_scalar_average_budget
end SpectralRadiusUpperTail

import SpectralRadiusUpperTail.TalagrandScalarMixing
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

namespace SpectralRadiusUpperTail
open MeasureTheory

/-- A measurable choice of interpolation parameter for the fiber induction. -/
noncomputable def talagrandWeight (a : ℝ) : ℝ :=
  if a ≤ 0 then 0 else max 0 (1+2*Real.log a)

lemma talagrandWeight_measurable : Measurable talagrandWeight := by
  unfold talagrandWeight
  exact Measurable.ite (measurableSet_le measurable_id measurable_const) measurable_const (by fun_prop)

lemma talagrandWeight_mem (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    0 ≤ talagrandWeight a ∧ talagrandWeight a ≤ 1 := by
  by_cases hzero : a ≤ 0
  · simp [talagrandWeight, hzero]
  · have hl := Real.log_nonpos ha ha1
    simp only [talagrandWeight, if_neg hzero]
    exact ⟨le_max_left _ _, max_le (by norm_num) (by linarith)⟩

lemma talagrandWeight_mixing_bound (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    Real.exp (-talagrandWeight a*Real.log a+(1-talagrandWeight a)^2/4) ≤ 2-a := by
  by_cases hzero : a ≤ 0
  · have he : a=0 := le_antisymm hzero ha
    subst a
    have hh := talagrand_exp_curve_bound (1/2) (by norm_num)
    have hp := (Real.exp_pos (-(1/2 : ℝ))).le
    norm_num [talagrandWeight] at hh ⊢
    linarith
  · have hapos : 0 < a := lt_of_not_ge hzero
    let x := -Real.log a
    have hx : 0 ≤ x := neg_nonneg.mpr (Real.log_nonpos ha ha1)
    have he : Real.exp (-x)=a := by dsimp [x]; rw [neg_neg, Real.exp_log hapos]
    by_cases hsmall : x ≤ 1/2
    · have hw : talagrandWeight a=1-2*x := by
        have hl : 0 ≤ 1+2*Real.log a := by dsimp [x] at hsmall; linarith
        simp only [talagrandWeight, if_neg hzero, max_eq_right hl]
        dsimp [x]
        ring
      rw [hw]
      have harg : -(1-2*x)*Real.log a+(1-(1-2*x))^2/4=x-x^2 := by dsimp [x]; ring
      rw [harg]
      have hh := talagrand_exp_curve_bound x hx
      rw [he] at hh
      linarith
    · have hw : talagrandWeight a=0 := by
        have hl : 1+2*Real.log a ≤ 0 := by dsimp [x] at hsmall; linarith
        simp only [talagrandWeight, if_neg hzero, max_eq_left hl]
      rw [hw]
      have hh := talagrand_exp_curve_bound (1/2) (by norm_num)
      have he' : a ≤ Real.exp (-(1/2 : ℝ)) := by
        rw [← he]
        exact Real.exp_le_exp.mpr (by linarith)
      norm_num at hh ⊢
      linarith

#print axioms talagrandWeight_measurable
#print axioms talagrandWeight_mem
#print axioms talagrandWeight_mixing_bound
end SpectralRadiusUpperTail

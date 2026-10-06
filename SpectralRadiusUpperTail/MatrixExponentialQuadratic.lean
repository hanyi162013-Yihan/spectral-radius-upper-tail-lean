import Mathlib.Analysis.Matrix.Order
import SpectralRadiusUpperTail.MatrixNormTransport
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith

namespace SpectralRadiusUpperTail
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder

lemma real_exp_le_one_add_sq {x : ℝ} (hx : ‖x‖ ≤ 1) :
    Real.exp x ≤ 1+x+x^2 := by
  have hh := Real.norm_exp_sub_one_sub_id_le hx
  have he := (le_abs_self (Real.exp x-1-x)).trans hh
  simpa only [Real.norm_eq_abs, sq_abs] using (by linarith : Real.exp x ≤ 1+x+‖x‖^2)

variable {𝕂 : Type*} [RCLike 𝕂] {ι : Type*} [Fintype ι] [DecidableEq ι]
  [Nonempty ι]

attribute [local instance] matrixL2RealNormedAlgebra

/-- Spectral functional calculus proves the quadratic matrix exponential
bound in the semidefinite order. The norm is the Euclidean operator norm. -/
theorem matrix_exp_le_one_add_square {A : Matrix ι ι 𝕂}
    (hA : A.IsHermitian) (hn : ‖A‖ ≤ 1) :
    NormedSpace.exp A ≤ 1+A+A^2 := by
  have hA' : IsSelfAdjoint A := hA
  have hc : cfc (fun x : ℝ => 1+x+x^2) A = 1+A+A^2 := by
    rw [cfc_add A (fun x : ℝ => 1+x) (fun x => x^2),
      cfc_const_add (p := IsSelfAdjoint) 1 (fun x : ℝ => x) A (ha := hA'),
      cfc_pow_id (R := ℝ) (p := IsSelfAdjoint) A 2 hA',
      cfc_id' ℝ A hA', map_one]
  rw [← CFC.real_exp_eq_normedSpace_exp hA', ← hc]
  apply (cfc_le_iff Real.exp (fun x : ℝ => 1+x+x^2) A (ha := hA')).2
  intro x hx
  have hxn : ‖x‖ ≤ ‖A‖ := spectrum.norm_le_norm_of_mem hx
  exact real_exp_le_one_add_sq (hxn.trans hn)

/-- A positive semidefinite contraction has square below itself. -/
theorem matrix_positive_contraction_square {D : Matrix ι ι 𝕂}
    (hD : D.PosSemidef) (hn : ‖D‖ ≤ 1) : D^2 ≤ D := by
  have hD' : IsSelfAdjoint D := hD.isHermitian
  have hh : cfc (fun x : ℝ => x^2) D ≤ cfc (fun x : ℝ => x) D := by
    apply (cfc_le_iff (fun x : ℝ => x^2) (fun x => x) D
      (ha := hD')).2
    intro x hx
    have hx0 : 0 ≤ x := spectrum_nonneg_of_nonneg hD.nonneg hx
    have hxn : ‖x‖ ≤ ‖D‖ := spectrum.norm_le_norm_of_mem hx
    have hx1 : x ≤ 1 := (le_abs_self x).trans (hxn.trans hn)
    nlinarith
  simpa only [cfc_pow_id (R := ℝ) (p := IsSelfAdjoint) D 2 hD',
    cfc_id' ℝ D hD'] using hh

#print axioms matrix_exp_le_one_add_square
#print axioms matrix_positive_contraction_square
end SpectralRadiusUpperTail

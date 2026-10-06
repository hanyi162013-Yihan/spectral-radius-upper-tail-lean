import SpectralRadiusUpperTail.GaussianMoments
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Data.Nat.Factorial.DoubleFactorial

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped BigOperators Nat

lemma standardNormal_mgf_eq :
    mgf id standardNormal = fun t : ℝ => Real.exp (t^2 / 2) := by
  simpa [standardNormal] using (mgf_id_gaussianReal (μ := 0) (v := 1))

lemma standardNormal_moment_eq_iteratedDeriv (k : ℕ) :
    (∫ x : ℝ, x^k ∂standardNormal) =
      iteratedDeriv k (fun t : ℝ => Real.exp (t^2 / 2)) 0 := by
  have hi : 0 ∈ interior (integrableExpSet id standardNormal) := by
    simp [standardNormal]
  have h := iteratedDeriv_mgf_zero hi k
  rw [standardNormal_mgf_eq] at h
  exact h.symm

lemma gaussian_mgf_deriv :
    deriv (fun t : ℝ => Real.exp (t^2 / 2)) = fun t => t * Real.exp (t^2 / 2) := by
  funext t
  convert (((hasDerivAt_id t).pow 2).div_const 2).exp.deriv using 1 <;>
    simp only [Pi.pow_apply, id_eq]
  all_goals ring

lemma iteratedDeriv_mul_id_at_zero (f : ℝ → ℝ) (k : ℕ)
    (hf : ContDiffAt ℝ (k+1) f 0) :
    iteratedDeriv (k+1) (fun t => t*f t) 0 = (k+1:ℝ) * iteratedDeriv k f 0 := by
  rw [iteratedDeriv_fun_mul (by fun_prop) hf]
  simp only [iteratedDeriv_fun_id_zero]
  rw [Finset.sum_eq_single 1]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact False.elim (h (Finset.mem_range.mpr (by omega)))

/-- Gaussian moment recursion derived from the actual moment-generating function. -/
theorem standardNormal_moment_add_two (k : ℕ) :
    (∫ x : ℝ, x^(k+2) ∂standardNormal) =
      (k+1:ℝ) * (∫ x : ℝ, x^k ∂standardNormal) := by
  rw [standardNormal_moment_eq_iteratedDeriv,
    standardNormal_moment_eq_iteratedDeriv, show k+2 = (k+1)+1 from rfl,
    iteratedDeriv_succ', gaussian_mgf_deriv]
  exact iteratedDeriv_mul_id_at_zero _ k (by fun_prop)

/-- Includes m=0 with the natural convention 0!!=1. -/
theorem standardNormal_even_moment (m : ℕ) :
    (∫ x : ℝ, x^(2*m) ∂standardNormal) = ((2*m-1)‼ : ℝ) := by
  induction m with
  | zero => simp [Nat.doubleFactorial]
  | succ m ih =>
    rw [show 2*(m+1) = 2*m+2 by omega, standardNormal_moment_add_two, ih]
    rw [show 2*m+2-1 = 2*m+1 by omega, Nat.doubleFactorial_add_one]
    push_cast
    ring

#print axioms standardNormal_moment_add_two
#print axioms standardNormal_even_moment
end SpectralRadiusUpperTail

import SpectralRadiusUpperTail.RealBernoulli
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable def standardNormal : Measure ℝ := gaussianReal 0 1

instance standardNormal_isProbabilityMeasure : IsProbabilityMeasure standardNormal := by
  unfold standardNormal
  infer_instance

theorem standardNormal_pow_integrable (k : ℕ) :
    Integrable (fun x : ℝ => x^k) standardNormal := by
  have h := (memLp_id_gaussianReal' (μ := 0) (v := 1) (k : ℝ≥0∞) (by simp)).integrable_norm_pow'
  apply h.mono' (by fun_prop)
  exact Filter.Eventually.of_forall (fun x => by simp)

theorem standardNormal_second_moment : (∫ x : ℝ, x^2 ∂standardNormal) = 1 := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_integral (by fun_prop)] at h
  simpa [standardNormal] using h

theorem standardNormal_odd_moment (m : ℕ) :
    (∫ x : ℝ, x^(2*m+1) ∂standardNormal) = 0 := by
  have hid : (∫ x : ℝ, x^(2*m+1) ∂standardNormal) =
      -(∫ x : ℝ, x^(2*m+1) ∂standardNormal) := by
    calc
      (∫ x : ℝ, x^(2*m+1) ∂standardNormal) =
          ∫ x : ℝ, x^(2*m+1) ∂standardNormal.map (fun x => -x) := by
            simp [standardNormal, gaussianReal_map_neg]
      _ = ∫ x : ℝ, (-x)^(2*m+1) ∂standardNormal := integral_map (by fun_prop) (by fun_prop)
      _ = -(∫ x : ℝ, x^(2*m+1) ∂standardNormal) := by
        simp [pow_add, pow_mul, integral_neg]
  linarith

theorem unit_second_even_moment_ge_one (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hint : ∀ k : ℕ, Integrable (fun x : ℝ => x^k) μ)
    (hsecond : (∫ x : ℝ, x^2 ∂μ) = 1) (m : ℕ) :
    1 ≤ ∫ x : ℝ, x^(2*m) ∂μ := by
  have hi₁ : Integrable (fun _x : ℝ => (1 : ℝ)) μ := integrable_const 1
  have hi₂ := hint 2
  have hisub : Integrable (fun x : ℝ => x^2-1) μ := by
    exact (hi₂.sub hi₁).congr (Filter.Eventually.of_forall (fun _ => rfl))
  have himul : Integrable (fun x : ℝ => (m:ℝ)*(x^2-1)) μ := hisub.const_mul (m:ℝ)
  have hil : Integrable (fun x : ℝ => 1+(m:ℝ)*(x^2-1)) μ := by
    exact (hi₁.add himul).congr (Filter.Eventually.of_forall (fun _ => rfl))
  have h := integral_mono hil (hint (2*m)) (fun x => by
    rw [pow_mul]
    exact one_add_mul_sub_le_pow (by nlinarith [sq_nonneg x]) m)
  have hmean : (∫ x : ℝ, 1+(m:ℝ)*(x^2-1) ∂μ) = 1 := by
    rw [integral_add hi₁ himul,
      integral_const_mul, integral_sub hi₂ hi₁, hsecond]
    simp
  rw [hmean] at h
  exact h

theorem standardNormal_even_moment_ge_one (m : ℕ) :
    1 ≤ ∫ x : ℝ, x^(2*m) ∂standardNormal :=
  unit_second_even_moment_ge_one standardNormal standardNormal_pow_integrable
    standardNormal_second_moment m

theorem standardNormal_moment_nonneg (k : ℕ) :
    0 ≤ ∫ x : ℝ, x^k ∂standardNormal := by
  obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' k
  · rw [hm]
    exact le_trans (by norm_num) (standardNormal_even_moment_ge_one m)
  · rw [hm, standardNormal_odd_moment]

/-- Actual sign and Gaussian measures, with no postulated Gaussian moment formula. -/
theorem sign_moment_le_standardNormal (k : ℕ) :
    (∫ x : ℝ, x^k ∂signMeasure) ≤ ∫ x : ℝ, x^k ∂standardNormal := by
  obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' k
  · rw [hm, sign_even_moment]
    exact standardNormal_even_moment_ge_one m
  · rw [hm, sign_odd_moment, standardNormal_odd_moment]

theorem sign_moment_nonneg (k : ℕ) : 0 ≤ ∫ x : ℝ, x^k ∂signMeasure := by
  obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' k
  · rw [hm, sign_even_moment]; norm_num
  · rw [hm, sign_odd_moment]

#print axioms standardNormal_pow_integrable
#print axioms standardNormal_second_moment
#print axioms standardNormal_odd_moment
#print axioms sign_moment_le_standardNormal
end SpectralRadiusUpperTail

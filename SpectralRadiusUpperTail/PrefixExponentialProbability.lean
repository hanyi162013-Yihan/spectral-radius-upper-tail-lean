import SpectralRadiusUpperTail.PrefixSafeEvent
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Real

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]

/-- Exponential Markov bound for an actual norm event. -/
lemma norm_probability_le_squareExp (P : Measure Ω) [IsFiniteMeasure P]
    (Y : Ω → E) (c M R : ℝ) (hc : 0 ≤ c) (hR : 0 ≤ R)
    (hi : Integrable (fun x => Real.exp (c*‖Y x‖^2)) P)
    (hb : (∫ x, Real.exp (c*‖Y x‖^2) ∂P) ≤ M) :
    P.real {x | R < ‖Y x‖} ≤ M*Real.exp (-c*R^2) := by
  have hsub : {x | R < ‖Y x‖} ⊆
      {x | Real.exp (c*R^2) ≤ Real.exp (c*‖Y x‖^2)} := by
    intro x hx
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left ((sq_le_sq₀ hR (norm_nonneg _)).mpr hx.le) hc
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun x => Real.exp_nonneg (c*‖Y x‖^2))) hi (Real.exp (c*R^2))
  have hh := (mul_le_mul_of_nonneg_left (measureReal_mono (μ := P) hsub)
    (Real.exp_nonneg (c*R^2))).trans hm
  have hdiv : P.real {x | R < ‖Y x‖} ≤ M/Real.exp (c*R^2) :=
    (le_div_iff₀ (Real.exp_pos _)).mpr (by simpa only [mul_comm] using hh.trans hb)
  convert! hdiv using 1
  rw [div_eq_mul_inv, ← Real.exp_neg]
  congr 2
  ring

lemma prefixSafeEvent_compl {E : Type*} [NormedAddCommGroup E]
    (Y : ℕ → Ω → E) (R : ℝ) (n : ℕ) :
    (prefixSafeEvent Y R n)ᶜ = ⋃ k ∈ Finset.range (n+1), {x | R < ‖Y k x‖} := by
  ext x
  simp [prefixSafeEvent, not_forall, Nat.lt_succ_iff]

/-- A finite union over all actual prefixes; no prefix independence is used. -/
theorem prefixSafeEvent_compl_probability (P : Measure Ω) [IsFiniteMeasure P]
    (Y : ℕ → Ω → E) (c M R : ℝ) (hc : 0 ≤ c) (hR : 0 ≤ R) (n : ℕ)
    (hi : ∀ k ≤ n, Integrable (fun x => Real.exp (c*‖Y k x‖^2)) P)
    (hb : ∀ k ≤ n, (∫ x, Real.exp (c*‖Y k x‖^2) ∂P) ≤ M) :
    P.real (prefixSafeEvent Y R n)ᶜ ≤ (n+1 : ℕ)*(M*Real.exp (-c*R^2)) := by
  rw [prefixSafeEvent_compl]
  apply (measureReal_biUnion_finset_le _ _).trans
  calc
    _ ≤ ∑ k ∈ Finset.range (n+1), M*Real.exp (-c*R^2) := by
      apply Finset.sum_le_sum
      intro k hk
      have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      exact norm_probability_le_squareExp P (Y k) c M R hc hR (hi k hk') (hb k hk')
    _ = _ := by simp

#print axioms prefixSafeEvent_compl_probability
end SpectralRadiusUpperTail

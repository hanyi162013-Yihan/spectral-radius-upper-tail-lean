import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology

lemma integral_lower_of_floor (Ω : Type*) [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Ω → ℝ)
    (hF : Measurable F) (hi : Integrable F μ) (m a : ℝ)
    (hm : ∀ x, m ≤ F x) :
    a-(a-m)*μ.real {x | F x < a} ≤ ∫ x, F x ∂μ := by
  let E := {x | F x < a}
  have hE : MeasurableSet E := measurableSet_lt hF measurable_const
  have hInd : Integrable (E.indicator (fun _ : Ω => (1 : ℝ))) μ :=
    (integrable_const _).indicator hE
  have hpoint (x : Ω) : a ≤ F x+(a-m)*E.indicator (fun _ => (1 : ℝ)) x := by
    by_cases hx : x ∈ E
    · rw [Set.indicator_of_mem hx]
      linarith [hm x]
    · rw [Set.indicator_of_notMem hx]
      have hh : a ≤ F x := le_of_not_gt hx
      linarith
  have hh := integral_mono (integrable_const a) (hi.add (hInd.const_mul (a-m))) hpoint
  change (∫ x : Ω, a ∂μ) ≤ ∫ x, F x+(a-m)*E.indicator (fun _ => (1 : ℝ)) x ∂μ at hh
  rw [integral_const, integral_add hi (hInd.const_mul (a-m)), integral_const_mul,
    integral_indicator_const (1 : ℝ) hE] at hh
  simp only [probReal_univ, smul_eq_mul, one_mul, mul_one] at hh
  linarith

lemma eventually_integral_lower_of_probability (Ω : ℕ → Type*)
    [∀ n, MeasurableSpace (Ω n)] (μ : (n : ℕ) → Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)] (F : (n : ℕ) → Ω n → ℝ)
    (hF : ∀ n, Measurable (F n))
    (hi : ∀ᶠ n in atTop, Integrable (F n) (μ n)) (m a : ℝ)
    (hm : ∀ n x, m ≤ F n x)
    (hprob : ∀ δ : ℝ, 0 < δ → Tendsto
      (fun n => (μ n).real {x | F n x < a-δ}) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, a-ε ≤ ∫ x, F n x ∂μ n := by
  have hh := (hprob (ε/2) (by positivity)).const_mul (a-ε/2-m)
  simp only [mul_zero] at hh
  have he := (tendsto_order.mp hh).2 (ε/2) (by positivity)
  filter_upwards [hi, he] with n hin hn
  have hl := integral_lower_of_floor (Ω n) (μ n) (F n) (hF n) hin m (a-ε/2) (hm n)
  linarith

#print axioms integral_lower_of_floor
#print axioms eventually_integral_lower_of_probability
end SpectralRadiusUpperTail

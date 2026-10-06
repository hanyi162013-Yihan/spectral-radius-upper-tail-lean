import SpectralRadiusUpperTail.TiltGoodIntersection
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped ENNReal Topology

lemma change_measure_half_event_log_lower {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ≥0∞)
    (A B : Set Ω) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (t : ℝ) (hbound : ∀ x ∈ B, f x ≤ ENNReal.ofReal (Real.exp t))
    (hgood : 1/2 ≤ (μ.withDensity f).real (A ∩ B)) :
    -t-Real.log 2 ≤ Real.log (μ.real A) := by
  have hc0 : ENNReal.ofReal (Real.exp t) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos t))
  have hh := change_measure_good_event μ f A B hA hB
    (ENNReal.ofReal (Real.exp t)) hc0 ENNReal.ofReal_ne_top hbound
  have hr := ENNReal.toReal_mono (measure_ne_top _ _) hh
  simp only [ENNReal.toReal_div,ENNReal.toReal_ofReal (Real.exp_pos t).le] at hr
  have hlow : (1/2)/Real.exp t ≤ μ.real A :=
    (div_le_div_of_nonneg_right hgood (Real.exp_pos t).le).trans hr
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (1/2)/Real.exp t) hlow
  rw [Real.log_div (by norm_num : (1/2 : ℝ) ≠ 0) (Real.exp_ne_zero t),Real.log_exp,
    Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0),Real.log_one] at hlog
  linarith

lemma change_measure_eventual_log_lower
    (Ω : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)]
    (μ : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (f : (n : ℕ) → Ω n → ℝ≥0∞) [∀ n, IsProbabilityMeasure ((μ n).withDensity (f n))]
    (A B : (n : ℕ) → Set (Ω n))
    (hA : ∀ n, MeasurableSet (A n)) (hB : ∀ n, MeasurableSet (B n))
    (ha : Tendsto (fun n => ((μ n).withDensity (f n)).real ((A n)ᶜ)) atTop (𝓝 0))
    (hb : Tendsto (fun n => ((μ n).withDensity (f n)).real ((B n)ᶜ)) atTop (𝓝 0))
    (C : ℝ) (hbound : ∀ᶠ n in atTop, ∀ x ∈ B n, f n x ≤ ENNReal.ofReal (Real.exp ((n : ℝ)*C)))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, -C-ε ≤ Real.log ((μ n).real (A n))/(n : ℝ) := by
  have hg := probability_inter_eventually_half Ω (fun n => (μ n).withDensity (f n)) A B hA hB ha hb
  have ht : Tendsto (fun n : ℕ => Real.log 2/(n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hs := (tendsto_order.1 ht).2 ε hε
  filter_upwards [hg,hbound,hs,eventually_ge_atTop (1 : ℕ)] with n hn hnb hns hn1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hh := change_measure_half_event_log_lower (μ n) (f n) (A n) (B n) (hA n) (hB n)
    ((n : ℝ)*C) hnb hn
  apply (le_div_iff₀ hnpos).mpr
  have hsmall := (div_lt_iff₀ hnpos).mp hns
  nlinarith

#print axioms change_measure_half_event_log_lower
#print axioms change_measure_eventual_log_lower
end SpectralRadiusUpperTail

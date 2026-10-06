import SpectralRadiusUpperTail.TiltGoodIntersection
import SpectralRadiusUpperTail.FlatSpectralLikelihood

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped ENNReal Topology

/-- An event typical under an absolutely continuous probability tilt has positive
original probability. This also prevents the `Real.log 0 = 0` convention from
weakening a logarithmic lower-bound statement. -/
lemma original_event_eventually_positive
    (Ω : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)]
    (μ ν : (n : ℕ) → Measure (Ω n))
    [∀ n, IsFiniteMeasure (μ n)] [∀ n, IsProbabilityMeasure (ν n)]
    (hac : ∀ n, ν n ≪ μ n) (A : (n : ℕ) → Set (Ω n))
    (hA : ∀ n, MeasurableSet (A n))
    (hgood : Tendsto (fun n => (ν n).real (A n)ᶜ) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, 0 < (μ n).real (A n) := by
  have he := (tendsto_order.1 hgood).2 1 zero_lt_one
  filter_upwards [he] with n hn
  have hsum := measureReal_add_measureReal_compl (μ := ν n) (hA n)
  have hν : 0 < (ν n).real (A n) := by
    have h1 : (ν n).real Set.univ = 1 := by simp [Measure.real]
    rw [h1] at hsum
    linarith
  apply ENNReal.toReal_pos ?_ (measure_ne_top _ _)
  intro hz
  have hvz := hac n hz
  have : (ν n).real (A n) = 0 := by simp [Measure.real, hvz]
  linarith

lemma exponential_lower_of_log_lower (p I ε : ℝ) (n : ℕ)
    (hp : 0 < p) (hn : 0 < n)
    (h : -I-ε ≤ Real.log p/(n : ℝ)) :
    Real.exp ((n : ℝ)*(-I-ε)) ≤ p := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hh := (le_div_iff₀ hnR).mp h
  rw [mul_comm] at hh
  simpa only [Real.exp_log hp] using Real.exp_le_exp.mpr hh

#print axioms original_event_eventually_positive
#print axioms exponential_lower_of_log_lower
end SpectralRadiusUpperTail

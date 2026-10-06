import SpectralRadiusUpperTail.UpperMeanFromProbability

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology

lemma eventually_integral_upper_of_probability (Ω : ℕ → Type*)
    [∀ n, MeasurableSpace (Ω n)] (μ : (n : ℕ) → Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)] (F : (n : ℕ) → Ω n → ℝ)
    (hF : ∀ n, Measurable (F n))
    (hi : ∀ᶠ n in atTop, Integrable (F n) (μ n))
    (h2 : ∀ᶠ n in atTop, Integrable (fun x => F n x^2) (μ n)) (a B : ℝ) (ha : 0 ≤ a)
    (hB : 0 ≤ B) (hbound : ∀ᶠ n in atTop, (∫ x, F n x^2 ∂μ n) ≤ B)
    (hprob : ∀ δ : ℝ, 0 < δ → Tendsto
      (fun n => (μ n).real {x | a+δ < F n x}) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, (∫ x, F n x ∂μ n) ≤ a+ε := by
  let K := 4*(B+1)/ε
  have hK : 0 < K := by dsimp [K]; positivity
  have hBK : B/K < ε/4 := by
    apply (div_lt_iff₀ hK).mpr
    dsimp [K]
    field_simp
    <;> nlinarith
  have ht := (hprob (ε/2) (by positivity)).const_mul K
  simp only [mul_zero] at ht
  have hp := (tendsto_order.mp ht).2 (ε/4) (by positivity)
  filter_upwards [hi, h2, hbound, hp] with n hin h2n hbn hpn
  have hh := integral_upper_of_second_moment (Ω n) (μ n) (F n) (hF n) hin h2n
    (a+ε/2) K (by positivity) hK
  have hm := div_le_div_of_nonneg_right hbn hK.le
  linarith

#print axioms eventually_integral_upper_of_probability
end SpectralRadiusUpperTail

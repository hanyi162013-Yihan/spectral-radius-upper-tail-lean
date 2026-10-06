import SpectralRadiusUpperTail.UpperMeanLimit

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology

lemma eventually_uniform_integral_upper_of_probability (Ω : ℕ → Type*)
    [∀ n, MeasurableSpace (Ω n)] (μ : (n : ℕ) → Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)] (ι : Type*) (F : (n : ℕ) → ι → Ω n → ℝ)
    (hF : ∀ n i, Measurable (F n i))
    (hi : ∀ᶠ n in atTop, ∀ i, Integrable (F n i) (μ n))
    (h2 : ∀ᶠ n in atTop, ∀ i, Integrable (fun x => F n i x^2) (μ n))
    (a : ι → ℝ) (B : ℝ) (ha : ∀ i, 0 ≤ a i) (hB : 0 ≤ B)
    (hbound : ∀ᶠ n in atTop, ∀ i, (∫ x, F n i x^2 ∂μ n) ≤ B)
    (hprob : ∀ δ : ℝ, 0 < δ → Tendsto
      (fun n => (μ n).real {x | ∃ i, a i+δ < F n i x}) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ i, (∫ x, F n i x ∂μ n) ≤ a i+ε := by
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
  intro i
  have hh := integral_upper_of_second_moment (Ω n) (μ n) (F n i) (hF n i) (hin i) (h2n i)
    (a i+ε/2) K (by have := ha i; positivity) hK
  have hm := div_le_div_of_nonneg_right (hbn i) hK.le
  have hpi : (μ n).real {x | a i+ε/2 < F n i x} ≤
      (μ n).real {x | ∃ j, a j+ε/2 < F n j x} :=
    measureReal_mono (μ := μ n) (fun _ hx => ⟨i, hx⟩)
  have hpim := mul_le_mul_of_nonneg_left hpi hK.le
  linarith

#print axioms eventually_uniform_integral_upper_of_probability
end SpectralRadiusUpperTail

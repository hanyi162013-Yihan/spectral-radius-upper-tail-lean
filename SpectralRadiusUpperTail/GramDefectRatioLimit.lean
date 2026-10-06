import SpectralRadiusUpperTail.GramDefectRatioPolynomial
import SpectralRadiusUpperTail.DyadicOrderAsymptotics

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]

lemma gramDefectRatio_dyadic_tendsto (μ : Measure 𝕂) (c : ℝ) (hc : 0 < c) (m : ℕ) :
    Tendsto (fun n => gramDefectRatio μ c m (dyadicMomentOrder 80 n) n) atTop (𝓝 0) := by
  have ht := (dyadicMomentOrder_ratio_tendsto 78 80 (by decide)).const_mul
    (gramDefectPolynomialConstant μ c m)
  simp only [mul_zero] at ht
  apply squeeze_zero _ _
    (show Tendsto (fun n : ℕ => gramDefectPolynomialConstant μ c m *
      (dyadicMomentOrder 80 n : ℝ)^78/n) atTop (𝓝 0) by
      simpa only [mul_div_assoc] using ht)
  · intro n
    have ha : 0 ≤ signedWordMomentBase μ c (2*(dyadicMomentOrder 80 n*m)) :=
      (by norm_num : (0 : ℝ) ≤ 1).trans (signedWordMomentBase_one_le μ c hc _)
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg ha 6)) (Nat.cast_nonneg _)
  · intro n
    exact gramDefectRatio_le_polynomial μ c hc m _ n (dyadicMomentOrder_pos 80 n)

lemma gramDefectRatio_dyadic_eventually (μ : Measure 𝕂) (c : ℝ) (hc : 0 < c) (m : ℕ) :
    ∀ᶠ n in atTop, gramDefectRatio μ c m (dyadicMomentOrder 80 n) n ≤ 1/2 :=
  (gramDefectRatio_dyadic_tendsto μ c hc m).eventually_le_const (by norm_num)

#print axioms gramDefectRatio_dyadic_tendsto
#print axioms gramDefectRatio_dyadic_eventually
end SpectralRadiusUpperTail

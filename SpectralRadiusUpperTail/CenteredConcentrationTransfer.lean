import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory

lemma centered_concentration_transfer {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [IsFiniteMeasure μ] (f g : E → ℝ) (δ : ℝ)
    (hmean : |(∫ x, f x ∂μ)-(∫ x, g x ∂μ)| ≤ δ/4) :
    μ.real {x | δ < |f x-(∫ y, f y ∂μ)|} ≤
      μ.real {x | δ/2 < |g x-(∫ y, g y ∂μ)|} +
      μ.real {x | δ/4 < |f x-g x|} := by
  have hsub : {x | δ < |f x-(∫ y, f y ∂μ)|} ⊆
      {x | δ/2 < |g x-(∫ y, g y ∂μ)|} ∪ {x | δ/4 < |f x-g x|} := by
    intro x hx
    by_contra hnot
    have ha : |g x-(∫ y, g y ∂μ)| ≤ δ/2 := by
      by_contra hn
      exact hnot (Or.inl (lt_of_not_ge hn))
    have hb : |f x-g x| ≤ δ/4 := by
      by_contra hn
      exact hnot (Or.inr (lt_of_not_ge hn))
    have ht : |f x-(∫ y, f y ∂μ)| ≤ |f x-g x|+
        |g x-(∫ y, g y ∂μ)|+|(∫ y, g y ∂μ)-(∫ y, f y ∂μ)| := by
      calc
        _ = |((f x-g x)+(g x-(∫ y, g y ∂μ)))+((∫ y, g y ∂μ)-(∫ y, f y ∂μ))| := by congr 1; ring
        _ ≤ |(f x-g x)+(g x-(∫ y, g y ∂μ))|+|(∫ y, g y ∂μ)-(∫ y, f y ∂μ)| := abs_add_le ((f x-g x)+(g x-(∫ y, g y ∂μ))) ((∫ y, g y ∂μ)-(∫ y, f y ∂μ))
        _ ≤ _ := add_le_add (abs_add_le (f x-g x) (g x-(∫ y, g y ∂μ))) le_rfl
    rw [abs_sub_comm (∫ y, g y ∂μ) (∫ y, f y ∂μ)] at ht
    change δ < |f x-(∫ y, f y ∂μ)| at hx
    linarith
  exact (measureReal_mono hsub (measure_ne_top _ _)).trans (measureReal_union_le _ _)

lemma centered_concentration_transfer_of_integral_error {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [IsFiniteMeasure μ] (f g : E → ℝ) (hf : Integrable f μ)
    (hg : Integrable g μ) (δ : ℝ) (herr : (∫ x, |f x-g x| ∂μ) ≤ δ/4) :
    μ.real {x | δ < |f x-(∫ y, f y ∂μ)|} ≤
      μ.real {x | δ/2 < |g x-(∫ y, g y ∂μ)|} +
      μ.real {x | δ/4 < |f x-g x|} := by
  apply centered_concentration_transfer
  rw [← integral_sub hf hg]
  exact abs_integral_le_integral_abs.trans herr

#print axioms centered_concentration_transfer
#print axioms centered_concentration_transfer_of_integral_error
end SpectralRadiusUpperTail

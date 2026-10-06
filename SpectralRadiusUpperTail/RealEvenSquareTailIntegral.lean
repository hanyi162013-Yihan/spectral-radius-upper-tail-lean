import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Set
open scoped ENNReal

/-- Reflection combines the two exterior intervals for an even
nonnegative function, without any integrability assumption. -/
theorem real_even_square_tail_lintegral (r : ℝ) (hr : 0 ≤ r)
    (f : ℝ → ℝ≥0∞) (heven : ∀ x, f (-x)=f x) :
    (∫⁻ x in {x : ℝ | r^2 < x^2}, f x) = 2 * ∫⁻ x in Ioi r, f x := by
  have hset : {x : ℝ | r^2 < x^2}=Ioi r ∪ Iio (-r) := by
    ext x
    change r^2 < x^2 ↔ r < x ∨ x < -r
    constructor
    · intro hx
      by_cases hp : r < x
      · exact Or.inl hp
      · right
        by_contra hn
        have h₁ : 0 ≤ r-x := by linarith
        have h₂ : 0 ≤ r+x := by linarith
        nlinarith [mul_nonneg h₁ h₂]
    · rintro (hx|hx)
      · nlinarith [mul_pos (by linarith : 0 < x-r) (by linarith : 0 < x+r)]
      · nlinarith [mul_pos (by linarith : 0 < r-x) (by linarith : 0 < -r-x)]
  have hdisj : Disjoint (Ioi r) (Iio (-r)) := by
    apply disjoint_left.mpr
    intro x hx hy
    simp only [mem_Ioi,mem_Iio] at hx hy
    linarith
  have hn := (Measure.measurePreserving_neg (volume : Measure ℝ)).setLIntegral_comp_preimage_emb
    (Homeomorph.neg ℝ).measurableEmbedding f (Iio (-r))
  have hpre : (fun x : ℝ => -x) ⁻¹' Iio (-r)=Ioi r := by
    ext x
    simp
  rw [hpre] at hn
  simp_rw [heven] at hn
  rw [hset,lintegral_union measurableSet_Iio hdisj,← hn,two_mul]

#print axioms real_even_square_tail_lintegral
end SpectralRadiusUpperTail

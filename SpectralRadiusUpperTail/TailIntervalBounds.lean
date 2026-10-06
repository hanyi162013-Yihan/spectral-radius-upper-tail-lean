import SpectralRadiusUpperTail.ExponentialDifference
import SpectralRadiusUpperTail.ExponentialBoundsLogLimit
import Mathlib.MeasureTheory.Measure.Real

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology

lemma interval_mass_ge_tail_difference {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → ℝ) (a b : ℝ) :
    μ.real {x | a < X x}-μ.real {x | b ≤ X x} ≤ μ.real {x | a < X x ∧ X x < b} := by
  have hsub : {x | a < X x} ⊆ {x | a < X x ∧ X x < b} ∪ {x | b ≤ X x} := by
    intro x hx
    by_cases hb : X x < b
    · exact Or.inl ⟨hx, hb⟩
    · exact Or.inr (le_of_not_gt hb)
  have hh := (measureReal_mono (μ := μ) hsub (measure_ne_top _ _)).trans (measureReal_union_le _ _)
  linarith

lemma interval_exponential_lower_of_tails
    (Ω : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)]
    (μ : (n : ℕ) → Measure (Ω n)) [∀ n, IsFiniteMeasure (μ n)]
    (X : (n : ℕ) → Ω n → ℝ) (a b Ia Ib : ℝ) (hI : Ia < Ib)
    (hl : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      Real.exp ((n : ℝ)*(-Ia-ε)) ≤ (μ n).real {x | a < X n x})
    (hu : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      (μ n).real {x | b ≤ X n x} ≤ Real.exp ((n : ℝ)*(-Ib+ε)))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, Real.exp ((n : ℝ)*(-Ia-ε)) ≤
      (μ n).real {x | a < X n x ∧ X n x < b} := by
  let δ := min (ε/2) ((Ib-Ia)/4)
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδε : δ ≤ ε/2 := min_le_left _ _
  have hδI : δ ≤ (Ib-Ia)/4 := min_le_right _ _
  have hgap : -Ib+δ < -Ia-δ := by linarith
  filter_upwards [hl δ hδ, hu δ hδ,
    eventually_exponential_difference_lower (-Ia-δ) (-Ib+δ) (ε/2) hgap (by positivity)]
      with n hn hm hd
  have hmass := interval_mass_ge_tail_difference (μ n) (X n) a b
  have hbudget : Real.exp ((n : ℝ)*(-Ia-ε)) ≤ Real.exp ((n : ℝ)*((-Ia-δ)-ε/2)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg n))
  linarith

#print axioms interval_mass_ge_tail_difference
#print axioms interval_exponential_lower_of_tails
end SpectralRadiusUpperTail

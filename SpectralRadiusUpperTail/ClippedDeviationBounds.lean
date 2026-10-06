import SpectralRadiusUpperTail.ClippedTailNeighborhood
import SpectralRadiusUpperTail.ClosedUpperTailUpper
import SpectralRadiusUpperTail.RateSublevels

namespace SpectralRadiusUpperTail
open MeasureTheory Filter Set

/-- Exponential open/closed set formulation for max(1,X), with finite rate
Iβ on [1,∞) and infinite rate below one. Nonempty intersections cover the
finite infima; the final clause handles sets of infinite rate exactly. -/
def ClippedDeviationBounds
    (Ω : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)]
    (μ : (n : ℕ) → Measure (Ω n)) (X : (n : ℕ) → Ω n → ℝ) (β : ℝ) : Prop :=
  (∀ U : Set ℝ, IsOpen U → (U ∩ Ici 1).Nonempty → ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
    Real.exp ((n : ℝ)*(-sInf (rate β '' (U ∩ Ici 1))-ε)) ≤
      (μ n).real {ω | max 1 (X n ω) ∈ U}) ∧
  (∀ F : Set ℝ, IsClosed F → (F ∩ Ici 1).Nonempty → ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
    (μ n).real {ω | max 1 (X n ω) ∈ F} ≤
      Real.exp ((n : ℝ)*(-sInf (rate β '' (F ∩ Ici 1))+ε))) ∧
  (∀ n (B : Set ℝ), B ∩ Ici 1 = ∅ → (μ n).real {ω | max 1 (X n ω) ∈ B}=0)

lemma clipped_deviation_bounds_of_tails
    (Ω : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)]
    (μ : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (X : (n : ℕ) → Ω n → ℝ) (β : ℝ) (hβ : 0 < β)
    (htails : ∀ r : ℝ, 1 < r → ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      Real.exp ((n : ℝ)*(-rate β r-ε)) ≤ (μ n).real {x | r < X n x} ∧
      (μ n).real {x | r ≤ X n x} ≤ Real.exp ((n : ℝ)*(-rate β r+ε))) :
    ClippedDeviationBounds Ω μ X β := by
  have hctails : ∀ r : ℝ, 1 < r → ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      Real.exp ((n : ℝ)*(-rate β r-ε)) ≤ (μ n).real {x | r < max 1 (X n x)} ∧
      (μ n).real {x | r ≤ max 1 (X n x)} ≤ Real.exp ((n : ℝ)*(-rate β r+ε)) := by
    intro r hr ε hε
    simpa only [clipped_strict_tail _ r hr, clipped_closed_tail _ r hr] using htails r hr ε hε
  refine ⟨?_, ?_, ?_⟩
  · intro U hU hne ε hε
    by_cases h1 : 1 ∈ U
    · rw [rate_infimum_support_at_one β hβ.le U h1]
      simpa only [neg_zero, zero_sub, mul_neg, neg_mul] using
        clipped_open_neighborhood_one Ω μ X β hβ
          (fun r hr δ hδ => (htails r hr δ hδ).mono (fun _ h => h.2)) U hU h1 ε hε
    · obtain ⟨v, hv, hvlt⟩ := exists_lt_of_csInf_lt (hne.image (rate β))
        (show sInf (rate β '' (U ∩ Ici 1)) < sInf (rate β '' (U ∩ Ici 1))+ε/2 by linarith)
      obtain ⟨x, hx, rfl⟩ := hv
      have hx1 : 1 < x := by
        have hle : 1 ≤ x := hx.2
        by_contra hn
        have he : x=1 := le_antisymm (le_of_not_gt hn) hle
        exact h1 (he ▸ hx.1)
      filter_upwards [open_set_exponential_lower_above_one Ω μ
        (fun n ω => max 1 (X n ω)) β hβ hctails U hU x hx.1 hx1 (ε/2) (by positivity)] with n hn
      apply le_trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg n))) hn
      linarith
  · intro F hF hne ε hε
    by_cases h1 : 1 ∈ F
    · rw [rate_infimum_support_at_one β hβ.le F h1]
      filter_upwards [] with n
      apply (measureReal_le_one (μ := μ n)).trans
      apply Real.one_le_exp_iff.mpr
      simp only [neg_zero, zero_add]
      positivity
    · have hS1 : ∀ x ∈ F ∩ Ici 1, 1 < x := by
        intro x hx
        have hle : 1 ≤ x := hx.2
        by_contra hn
        have he : x=1 := le_antisymm (le_of_not_gt hn) hle
        exact h1 (he ▸ hx.1)
      have hh := closed_set_exponential_upper_above_one Ω μ (fun n ω => max 1 (X n ω)) β hβ
        (fun r hr δ hδ => (hctails r hr δ hδ).mono (fun _ h => h.2))
        (F ∩ Ici 1) (hF.inter isClosed_Ici) hne hS1 ε hε
      have he (n : ℕ) : {ω | max 1 (X n ω) ∈ F ∩ Ici 1}={ω | max 1 (X n ω) ∈ F} := by
        ext ω
        change (max 1 (X n ω) ∈ F ∧ 1 ≤ max 1 (X n ω)) ↔ max 1 (X n ω) ∈ F
        simp only [le_max_left, and_true]
      simpa only [he] using hh
  · intro n B hB
    have he : {ω | max 1 (X n ω) ∈ B} = (∅ : Set (Ω n)) := by
      apply eq_empty_iff_forall_notMem.mpr
      intro ω hω
      have hh : max 1 (X n ω) ∈ B ∩ Ici 1 := ⟨hω, by change 1 ≤ max 1 (X n ω); exact le_max_left _ _⟩
      rw [hB] at hh
      exact hh
    rw [he, measureReal_empty]

#print axioms clipped_deviation_bounds_of_tails
end SpectralRadiusUpperTail

import SpectralRadiusUpperTail.RegularizedLogSlope

namespace SpectralRadiusUpperTail

noncomputable def regularizedConvexSlope₁ (τ x : ℝ) : ℝ :=
  if x ≤ τ then regularizedLogSlope τ x else 1/τ

noncomputable def regularizedConvexSlope₂ (τ x : ℝ) : ℝ :=
  if x ≤ τ then 0 else 1/τ-regularizedLogSlope τ x

lemma regularizedConvexSlopes_sub (τ x : ℝ) :
    regularizedConvexSlope₁ τ x-regularizedConvexSlope₂ τ x = regularizedLogSlope τ x := by
  unfold regularizedConvexSlope₁ regularizedConvexSlope₂
  split_ifs <;> ring

lemma regularizedConvexSlopes_bounds (τ x : ℝ) (hτ : 0 < τ) (hx : 0 ≤ x) :
    (0 ≤ regularizedConvexSlope₁ τ x ∧ regularizedConvexSlope₁ τ x ≤ 1/τ) ∧
    (0 ≤ regularizedConvexSlope₂ τ x ∧ regularizedConvexSlope₂ τ x ≤ 1/τ) := by
  have hl := regularizedLogSlope_nonneg τ x hx
  have hu := regularizedLogSlope_le τ x hτ
  unfold regularizedConvexSlope₁ regularizedConvexSlope₂
  split_ifs <;> constructor <;> constructor <;> first | assumption | positivity | linarith

lemma regularizedConvexSlope₁_monotone (τ : ℝ) (hτ : 0 < τ) :
    MonotoneOn (regularizedConvexSlope₁ τ) (Set.Ici 0) := by
  intro x hx y hy hxy
  unfold regularizedConvexSlope₁
  by_cases hyτ : y ≤ τ
  · rw [if_pos (hxy.trans hyτ), if_pos hyτ]
    exact regularizedLogSlope_monotone τ hτ ⟨hx, hxy.trans hyτ⟩ ⟨hy, hyτ⟩ hxy
  · rw [if_neg hyτ]
    split_ifs
    · exact regularizedLogSlope_le τ x hτ
    · exact le_refl _

lemma regularizedConvexSlope₂_monotone (τ : ℝ) (hτ : 0 < τ) :
    MonotoneOn (regularizedConvexSlope₂ τ) (Set.Ici 0) := by
  intro x hx y hy hxy
  unfold regularizedConvexSlope₂
  by_cases hxτ : x ≤ τ
  · rw [if_pos hxτ]
    split_ifs
    · exact le_refl _
    · exact sub_nonneg.mpr (regularizedLogSlope_le τ y hτ)
  · rw [if_neg hxτ, if_neg (not_le.mpr ((lt_of_not_ge hxτ).trans_le hxy))]
    exact sub_le_sub_left (regularizedLogSlope_antitone τ hτ
      (le_of_not_ge hxτ) ((le_of_not_ge hxτ).trans hxy) hxy) _

lemma regularizedConvexSlope₁_continuous (τ : ℝ) (hτ : 0 < τ) :
    Continuous (regularizedConvexSlope₁ τ) := by
  apply (regularizedLogSlope_continuous τ hτ).if_le continuous_const continuous_id continuous_const
  intro x hx
  change x = τ at hx
  subst x
  exact regularizedLogSlope_at_cutoff τ hτ

lemma regularizedConvexSlope₂_continuous (τ : ℝ) (hτ : 0 < τ) :
    Continuous (regularizedConvexSlope₂ τ) := by
  have he : regularizedConvexSlope₂ τ = fun x =>
      regularizedConvexSlope₁ τ x-regularizedLogSlope τ x := by
    funext x
    have h := regularizedConvexSlopes_sub τ x
    linarith
  rw [he]
  exact (regularizedConvexSlope₁_continuous τ hτ).sub (regularizedLogSlope_continuous τ hτ)

#print axioms regularizedConvexSlopes_sub
#print axioms regularizedConvexSlopes_bounds
#print axioms regularizedConvexSlope₁_monotone
#print axioms regularizedConvexSlope₂_monotone
#print axioms regularizedConvexSlope₁_continuous
#print axioms regularizedConvexSlope₂_continuous
end SpectralRadiusUpperTail

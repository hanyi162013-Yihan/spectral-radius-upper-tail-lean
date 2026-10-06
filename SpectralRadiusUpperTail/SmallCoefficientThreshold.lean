import SpectralRadiusUpperTail.GaussianRowRegressionMoment

namespace SpectralRadiusUpperTail

/-- Three fixed quadratic constraints admit one positive coefficient cutoff.
This is independent of the number of coefficients in the application. -/
lemma exists_pos_three_square_bounds (A B D p q ε : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hp : 0 < p) (hq : 0 < q) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ A*δ^2 < p ∧ B*δ^2 < q ∧ D*δ^2 < ε := by
  obtain ⟨δ₁, hδ₁, h₁⟩ := exists_pos_mul_lt hp A
  obtain ⟨δ₂, hδ₂, h₂⟩ := exists_pos_mul_lt hq B
  obtain ⟨δ₃, hδ₃, h₃⟩ := exists_pos_mul_lt hε D
  let δ := min 1 (min δ₁ (min δ₂ δ₃))
  have hδ : 0 < δ := lt_min (by norm_num) (lt_min hδ₁ (lt_min hδ₂ hδ₃))
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδ₁' : δ ≤ δ₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hδ₂' : δ ≤ δ₂ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδ₃' : δ ≤ δ₃ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hs : δ^2 ≤ δ := by nlinarith [mul_le_mul_of_nonneg_left hδ1 hδ.le]
  refine ⟨δ, hδ, ?_, ?_, ?_⟩
  · have hh := mul_le_mul_of_nonneg_left (hs.trans hδ₁') hA
    nlinarith only [hh, h₁]
  · have hh := mul_le_mul_of_nonneg_left (hs.trans hδ₂') hB
    nlinarith only [hh, h₂]
  · have hh := mul_le_mul_of_nonneg_left (hs.trans hδ₃') hD
    nlinarith only [hh, h₃]

#print axioms exists_pos_three_square_bounds
end SpectralRadiusUpperTail

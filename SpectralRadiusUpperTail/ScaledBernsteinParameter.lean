import SpectralRadiusUpperTail.BernsteinParameter

namespace SpectralRadiusUpperTail

/-- Optimize after normalizing an increment bound b and a variance bound V. -/
lemma scaled_bernstein_parameter {V b u : ℝ} (hV : 0 ≤ V) (hb : 0 < b) (hu : 0 < u) :
    ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1/2 ∧
      -s*(b⁻¹*u)+2*s^2*(b⁻¹^2*V) ≤ -u^2/(8*V+4*b*u) := by
  have hv : 0 ≤ b⁻¹^2*V := mul_nonneg (sq_nonneg _) hV
  have ht : 0 < b⁻¹*u := mul_pos (inv_pos.mpr hb) hu
  have hs := bernstein_parameter hv ht
  refine ⟨(b⁻¹*u)/(4*(b⁻¹^2*V)+2*(b⁻¹*u)), hs.1, hs.2.1, ?_⟩
  have he : -(b⁻¹*u)^2/(8*(b⁻¹^2*V)+4*(b⁻¹*u)) = -u^2/(8*V+4*b*u) := by
    have hd : 8*V+4*b*u ≠ 0 := by positivity
    have hd' : 8*(b⁻¹^2*V)+4*(b⁻¹*u) ≠ 0 := by positivity
    field_simp
    <;> ring
  exact hs.2.2.trans_eq he

#print axioms scaled_bernstein_parameter
end SpectralRadiusUpperTail

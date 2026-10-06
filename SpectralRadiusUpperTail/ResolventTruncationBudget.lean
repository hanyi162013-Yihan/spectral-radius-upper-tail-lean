import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

lemma exists_resolvent_truncation_threshold (B ε : ℝ) (hB : 0 < B) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ B*(3*δ) ≤ 1/2 ∧ 2*B^2*(3*δ) ≤ ε/4 := by
  let δ := min (1/(6*B)) (ε/(24*B^2))
  have hd : 0 < δ := lt_min (by positivity) (by positivity)
  refine ⟨δ,hd,?_,?_⟩
  · have hh := (le_div_iff₀ (by positivity : (0:ℝ) < 6*B)).mp
      (min_le_left (1/(6*B)) (ε/(24*B^2)))
    change δ*(6*B) ≤ 1 at hh
    nlinarith
  · have hh := (le_div_iff₀ (by positivity : (0:ℝ) < 24*B^2)).mp
      (min_le_right (1/(6*B)) (ε/(24*B^2)))
    change δ*(24*B^2) ≤ ε at hh
    nlinarith

#print axioms exists_resolvent_truncation_threshold
end SpectralRadiusUpperTail

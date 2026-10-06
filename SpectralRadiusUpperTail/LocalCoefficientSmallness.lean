import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

/-- A single coefficient threshold makes the local perturbation hypotheses
hold uniformly for every target inside the predictable cutoff. -/
lemma localCoefficientSmallness (C K d I δ b s : ℝ)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hd : 0 < d) (hI : 0 ≤ I)
    (hb : 0 ≤ b) (hbδ : b ≤ δ) (hδ : δ ≤ 1) (hs : s ≤ K)
    (hunit : (C*(K+2)/d)*δ ≤ 1)
    (herror : ((C*(K+2)/d)*δ)*I ≤ 1/2) :
    let u := (C*(K+2)/d)*b
    0 ≤ u ∧ u ≤ 1 ∧ C*b*(1+s+b) ≤ d*u ∧ u*I ≤ 1/2 := by
  let L := C*(K+2)/d
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hub : L*b ≤ L*δ := mul_le_mul_of_nonneg_left hbδ hL
  refine ⟨mul_nonneg hL hb, hub.trans hunit, ?_, ?_⟩
  · calc
      C*b*(1+s+b) ≤ C*b*(K+2) :=
        mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hC hb)
      _ = d*((C*(K+2)/d)*b) := by field_simp
  · exact (mul_le_mul_of_nonneg_right hub hI).trans herror

#print axioms localCoefficientSmallness
end SpectralRadiusUpperTail

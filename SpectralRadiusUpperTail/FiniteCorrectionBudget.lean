import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

lemma exists_finite_correction_threshold (m : ℕ) (L M ε : ℝ)
    (hL : 0 ≤ L) (hM : 0 ≤ M) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ k : ℕ, k ≤ m → (k : ℝ)^2*(2*(L*δ)*M) ≤ ε/4 := by
  let K := 2*(m : ℝ)^2*L*M
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let δ := ε/(4*(K+1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨δ,hδ,?_⟩
  intro k hk
  have hk' : (k : ℝ) ≤ m := by exact_mod_cast hk
  have hs := pow_le_pow_left₀ (Nat.cast_nonneg k) hk' 2
  have hp : (k : ℝ)^2*(2*(L*δ)*M) ≤ K*δ := by
    have hh := mul_le_mul_of_nonneg_right hs (by positivity : 0 ≤ 2*(L*δ)*M)
    exact hh.trans_eq (by dsimp [K]; ring)
  apply hp.trans
  dsimp [δ]
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4*(K+1))).mpr
  nlinarith

#print axioms exists_finite_correction_threshold
end SpectralRadiusUpperTail

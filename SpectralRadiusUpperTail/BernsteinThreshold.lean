import SpectralRadiusUpperTail.ScaledBernsteinParameter
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace SpectralRadiusUpperTail

/-- An explicit positive threshold turns the Bernstein exponent into -L. -/
lemma bernstein_threshold {V b L : ℝ} (hV : 0 ≤ V) (hb : 0 < b) (hL : 0 < L) :
    let u := 4*Real.sqrt (V*L)+8*b*L
    0 < u ∧ -u^2/(8*V+4*b*u) ≤ -L := by
  let u := 4*Real.sqrt (V*L)+8*b*L
  have hu : 0 < u := by dsimp [u]; positivity
  have hd : 0 < 8*V+4*b*u := by positivity
  have hs := Real.sq_sqrt (mul_nonneg hV hL.le)
  have hq : L*(8*V+4*b*u) ≤ u^2 := by
    dsimp [u]
    nlinarith [Real.sqrt_nonneg (V*L), mul_nonneg hb.le hL.le,
      mul_nonneg (mul_nonneg hb.le hL.le) (Real.sqrt_nonneg (V*L)),
      mul_nonneg hV hL.le, sq_nonneg (b*L)]
  exact ⟨hu, (div_le_iff₀ hd).2 (by nlinarith)⟩

#print axioms bernstein_threshold
end SpectralRadiusUpperTail

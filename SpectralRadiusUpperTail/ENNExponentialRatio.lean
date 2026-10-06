import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.ENNReal.Inv
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped ENNReal

lemma ennreal_exp_ratio (a b : ℝ) :
    (ENNReal.ofReal (Real.exp a))⁻¹*ENNReal.ofReal (Real.exp b) = ENNReal.ofReal (Real.exp (b-a)) := by
  rw [← ENNReal.ofReal_inv_of_pos (Real.exp_pos a), ← ENNReal.ofReal_mul (by positivity),
    ← Real.exp_neg, ← Real.exp_add]
  congr 2
  ring

#print axioms ennreal_exp_ratio
end SpectralRadiusUpperTail

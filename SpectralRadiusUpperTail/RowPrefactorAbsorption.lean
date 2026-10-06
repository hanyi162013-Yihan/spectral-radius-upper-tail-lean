import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

/-- Large targets pay for the missing prefactor through their squared energy. -/
lemma row_prefactor_absorb (f h h₀ E T K ε : ℝ)
    (hh₀ : 0 < h₀) (hh₀1 : h₀ ≤ 1) (hh : h₀ ≤ h) (hT : 0 ≤ T)
    (hK : 0 < K) (hε : 0 ≤ ε)
    (hall : f ≤ Real.exp (-E))
    (hsmall : T ≤ K^2 → f ≤ Real.exp ε*h*Real.exp (-E)) :
    f ≤ h*Real.exp (-E+ε+(T/K^2)*(-Real.log h₀)) := by
  have hlog : 0 ≤ -Real.log h₀ := neg_nonneg.mpr (Real.log_nonpos hh₀.le hh₀1)
  have hcost : 0 ≤ (T/K^2)*(-Real.log h₀) := mul_nonneg (div_nonneg hT (sq_nonneg K)) hlog
  by_cases ht : T ≤ K^2
  · apply (hsmall ht).trans
    calc
      Real.exp ε*h*Real.exp (-E) = h*Real.exp (-E+ε) := by rw [Real.exp_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (hh₀.le.trans hh)
  · have hratio : 1 ≤ T/K^2 := (le_div_iff₀ (sq_pos_of_pos hK)).mpr (by linarith)
    have hc := mul_le_mul_of_nonneg_right hratio hlog
    apply hall.trans
    calc
      Real.exp (-E) ≤ Real.exp (Real.log h₀+(-E+ε+(T/K^2)*(-Real.log h₀))) := by
        apply Real.exp_le_exp.mpr
        linarith
      _ = h₀*Real.exp (-E+ε+(T/K^2)*(-Real.log h₀)) := by
        rw [Real.exp_add, Real.exp_log hh₀]
      _ ≤ _ := mul_le_mul_of_nonneg_right hh (Real.exp_nonneg _)

/-- An additive replacement error becomes multiplicative on a bounded target range. -/
lemma additive_error_absorb (f g δ ε b : ℝ) (hb : 0 < b) (hbg : b ≤ g)
    (hε : 0 ≤ ε) (hδ : δ ≤ (Real.exp ε-1)*b) (hf : f ≤ g+δ) :
    f ≤ Real.exp ε*g := by
  have he : 0 ≤ Real.exp ε-1 := sub_nonneg.mpr (Real.one_le_exp hε)
  have hh := mul_le_mul_of_nonneg_left hbg he
  linarith

#print axioms row_prefactor_absorb
#print axioms additive_error_absorb
end SpectralRadiusUpperTail

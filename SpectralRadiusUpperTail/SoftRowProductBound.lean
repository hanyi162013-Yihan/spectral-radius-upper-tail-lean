import SpectralRadiusUpperTail.RowPrefactorAbsorption
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped BigOperators

lemma soft_prefactor_bounds (a q : ℝ) (ha : 0 < a) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    0 < a/(a+1) ∧ a/(a+1) ≤ 1 ∧ a/(a+1) ≤ a/(a+q) := by
  refine ⟨by positivity, (div_le_one (by positivity)).mpr (by linarith), ?_⟩
  exact div_le_div_of_nonneg_left ha.le (by positivity) (by linarith)

lemma soft_row_error_bound (f a q T K ε δ : ℝ)
    (ha : 0 < a) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hT : 0 ≤ T)
    (hK : 0 < K) (hε : 0 ≤ ε)
    (hall : f ≤ Real.exp (-T/(a+1)))
    (hlight : f ≤ (a/(a+q))*Real.exp (-T/(a+1))+δ)
    (hδ : δ ≤ (Real.exp ε-1)*((a/(a+1))*Real.exp (-K^2/(a+1)))) :
    f ≤ (a/(a+q))*Real.exp (-T/(a+1)+ε+(T/K^2)*(-Real.log (a/(a+1)))) := by
  obtain ⟨hp, hp1, hfloor⟩ := soft_prefactor_bounds a q ha hq hq1
  rw [neg_div]
  apply row_prefactor_absorb f (a/(a+q)) (a/(a+1)) (T/(a+1)) T K ε hp hp1 hfloor hT hK hε
    (by simpa only [neg_div] using hall)
  intro hTK
  have hg : (a/(a+1))*Real.exp (-K^2/(a+1)) ≤ (a/(a+q))*Real.exp (-T/(a+1)) := by
    apply mul_le_mul hfloor ?_ (Real.exp_nonneg _) (by positivity)
    apply Real.exp_le_exp.mpr
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  have hh := additive_error_absorb f ((a/(a+q))*Real.exp (-T/(a+1))) δ ε
    ((a/(a+1))*Real.exp (-K^2/(a+1))) (by positivity) hg hε hδ hlight
  simpa only [neg_div, mul_assoc] using hh

lemma soft_row_product_bound (n : ℕ) (f T : Fin n → ℝ) (h a K ε D : ℝ)
    (hf : ∀ i, 0 ≤ f i)
    (hrow : ∀ i, f i ≤ h*Real.exp (-T i/(a+1)+ε+(T i/K^2)*D)) :
    (∏ i, f i) ≤ h^n*Real.exp (-(∑ i, T i)/(a+1)+(n : ℝ)*ε+((∑ i, T i)/K^2)*D) := by
  calc
    _ ≤ ∏ i, h*Real.exp (-T i/(a+1)+ε+(T i/K^2)*D) :=
      Finset.prod_le_prod (fun i _ => hf i) (fun i _ => hrow i)
    _ = _ := by
      rw [Finset.prod_mul_distrib, ← Real.exp_sum]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      congr 2
      simp only [neg_div, Finset.sum_add_distrib, Finset.sum_div, Finset.sum_neg_distrib,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.sum_mul]

#print axioms soft_prefactor_bounds
#print axioms soft_row_error_bound
#print axioms soft_row_product_bound
end SpectralRadiusUpperTail

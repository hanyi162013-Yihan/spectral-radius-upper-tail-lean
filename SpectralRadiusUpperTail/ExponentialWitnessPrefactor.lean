import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped BigOperators

lemma exponential_witness_prefactor (m : ℕ) (u h₀ : ℝ) (h : Fin m → ℝ)
    (hu : 0 < u) (hh₀ : 0 ≤ h₀) (hh : ∀ i, 0 ≤ h i) :
    u^(m+1)/((h₀+2*u)*∏ i, (h i+2*u)) ≤
      (1/2 : ℝ)^m*(1/2)*∏ i, (((h i+2*u)/(2*u))⁻¹) := by
  have hp : 0 < ∏ i, (h i+2*u) := Finset.prod_pos (fun i _ => by linarith [hh i])
  have hden : 0 < h₀+2*u := by positivity
  have he : (1/2 : ℝ)^m*(1/2)*∏ i, (((h i+2*u)/(2*u))⁻¹) =
      (1/2)*(u^m/(∏ i, (h i+2*u))) := by
    simp_rw [inv_div]
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    calc
      _ = (1/2)*(((1/2 : ℝ)^m*(2*u)^m)/(∏ i, (h i+2*u))) := by ring
      _ = _ := by rw [← mul_pow, show (1/2 : ℝ)*(2*u) = u by ring]
  rw [he]
  have hhalf : u/(h₀+2*u) ≤ (1/2 : ℝ) := by
    apply (div_le_iff₀ hden).mpr
    linarith
  calc
    _ = (u/(h₀+2*u))*(u^m/(∏ i, (h i+2*u))) := by simp only [pow_succ, div_eq_mul_inv, mul_inv_rev]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hhalf (div_nonneg (pow_nonneg hu.le m) hp.le)

#print axioms exponential_witness_prefactor
end SpectralRadiusUpperTail

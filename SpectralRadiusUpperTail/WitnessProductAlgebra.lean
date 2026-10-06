import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped BigOperators

lemma witness_product_prefactor (m : ℕ) (u h₀ : ℝ) (h : Fin m → ℝ)
    (hu : 0 < u) (hh₀ : 0 ≤ h₀) (hh : ∀ i, 0 ≤ h i) :
    u^(m+1)/(((m+1 : ℕ) : ℝ)^m*((h₀+2*u)*∏ i, (h i+2*u))) ≤
      (1/2 : ℝ)*∏ i, ((((m+1 : ℕ) : ℝ)*(h i+2*u)/u)⁻¹) := by
  have hn : (0 : ℝ) < ((m+1 : ℕ) : ℝ) := by positivity
  have hp : 0 < ∏ i, (h i+2*u) := Finset.prod_pos (fun i _ => by linarith [hh i])
  have hfirst : 0 < h₀+2*u := by linarith
  have he : (∏ i, ((((m+1 : ℕ) : ℝ)*(h i+2*u)/u)⁻¹)) =
      u^m/(((m+1 : ℕ) : ℝ)^m*∏ i, (h i+2*u)) := by
    simp only [inv_div,Finset.prod_div_distrib,Finset.prod_mul_distrib,
      Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  rw [he]
  apply (div_le_iff₀ (mul_pos (pow_pos hn _) (mul_pos hfirst hp))).mpr
  have hnz : (((m+1 : ℕ) : ℝ)^m) ≠ 0 := ne_of_gt (pow_pos hn _)
  have heq : (1/2 : ℝ)*(u^m/(((m+1 : ℕ) : ℝ)^m*∏ i, (h i+2*u)))*
      (((m+1 : ℕ) : ℝ)^m*((h₀+2*u)*∏ i, (h i+2*u))) =
        u^m*(h₀+2*u)/2 := by
    field_simp
    <;> ring
  rw [heq,pow_succ]
  nlinarith [mul_nonneg (pow_nonneg hu.le m) hh₀]

#print axioms witness_product_prefactor
end SpectralRadiusUpperTail

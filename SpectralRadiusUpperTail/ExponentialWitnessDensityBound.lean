import SpectralRadiusUpperTail.ExponentialProductDensity
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped BigOperators

lemma exponential_tail_density_cancellation (N S a d k : ℝ) :
    (k*Real.exp (-S/2))*(Real.exp a*Real.exp (-d))*Real.exp (-(1/2 : ℝ)*(2*N-S)) =
      k*Real.exp (a-N)*Real.exp (-d) := by
  calc
    _ = k*(Real.exp (-S/2)*Real.exp a*Real.exp (-d)*Real.exp (-(1/2 : ℝ)*(2*N-S))) := by ring
    _ = k*Real.exp ((-S/2+a)+(-d)+(-(1/2 : ℝ)*(2*N-S))) := by
      rw [Real.exp_add, Real.exp_add, Real.exp_add]
    _ = k*Real.exp ((a-N)+(-d)) := by congr 2 <;> ring
    _ = _ := by rw [Real.exp_add]; ring

lemma exponential_witness_density_cancel {m : ℕ} (N u h₀ : ℝ) (h y : Fin m → ℝ)
    (hy : ∀ i, 0 ≤ y i) :
    (∏ i, exponentialPDFReal (1/2) (y i)) *
        (Real.exp (-N*h₀/u)*Real.exp (-(∑ i, (h i-h₀)*y i)/(2*u))) *
        Real.exp (-(1/2 : ℝ)*(2*N-∑ i, y i)) =
      (1/2 : ℝ)^m*Real.exp (-N*h₀/u-N)*Real.exp (-(∑ i, (h i-h₀)*y i)/(2*u)) := by
  rw [exponential_product_density_nonneg m (fun _ => 1/2) y hy]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hs : (∑ i, (1/2 : ℝ)*y i) = (∑ i, y i)/2 := by rw [← Finset.mul_sum]; ring
  rw [hs]
  simpa only [neg_div] using exponential_tail_density_cancellation N (∑ i, y i)
    (-N*h₀/u) ((∑ i, (h i-h₀)*y i)/(2*u)) ((1/2 : ℝ)^m)

lemma exponential_witness_density_lower {m : ℕ} (N u h₀ : ℝ) (h y r : Fin m → ℝ)
    (hu : 0 < u) (hy : ∀ i, 0 ≤ y i)
    (hr : ∀ i, (h i-h₀)/(2*u) ≤ r i) :
    (1/2 : ℝ)^m*Real.exp (-N*h₀/u-N)*Real.exp (-(∑ i, r i*y i)) ≤
      (∏ i, exponentialPDFReal (1/2) (y i)) *
        (Real.exp (-N*h₀/u)*Real.exp (-(∑ i, (h i-h₀)*y i)/(2*u))) *
        Real.exp (-(1/2 : ℝ)*(2*N-∑ i, y i)) := by
  rw [exponential_witness_density_cancel N u h₀ h y hy]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_right (hr i) (hy i))
  have he : (∑ i, (h i-h₀)/(2*u)*y i) = (∑ i, (h i-h₀)*y i)/(2*u) := by
    simp only [div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he] at hh
  simpa only [neg_div] using neg_le_neg hh

#print axioms exponential_tail_density_cancellation
#print axioms exponential_witness_density_cancel
#print axioms exponential_witness_density_lower
end SpectralRadiusUpperTail

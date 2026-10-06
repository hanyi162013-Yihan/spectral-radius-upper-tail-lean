import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped BigOperators

lemma normalized_weighted_energy_le {m : ℕ} (N u h₀ y₀ : ℝ) (h y : Fin m → ℝ)
    (hN : 0 < N) (hu : 0 < u) (hy : ∀ i, 0 ≤ y i) (hmin : ∀ i, h₀ ≤ h i)
    (htotal : 2*N ≤ y₀+∑ i, y i) :
    (N/u)*((h₀*y₀+∑ i, h i*y i)/(y₀+∑ i, y i)) ≤
      N*h₀/u+(∑ i, (h i-h₀)*y i)/(2*u) := by
  let T := y₀+∑ i, y i
  let D := ∑ i, (h i-h₀)*y i
  have hT : 0 < T := lt_of_lt_of_le (by positivity) htotal
  have hD : 0 ≤ D := Finset.sum_nonneg (fun i _ => mul_nonneg (sub_nonneg.mpr (hmin i)) (hy i))
  have he : h₀*y₀+∑ i, h i*y i = h₀*T+D := by
    dsimp [T, D]
    simp_rw [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  rw [he]
  change N/u*((h₀*T+D)/T) ≤ N*h₀/u+D/(2*u)
  have hid : N/u*((h₀*T+D)/T) = N*h₀/u+(N*D)/(u*T) := by
    field_simp
  rw [hid]
  apply add_le_add le_rfl
  apply (div_le_div_iff₀ (mul_pos hu hT) (by positivity : 0 < 2*u)).mpr
  have hh := mul_le_mul_of_nonneg_left htotal (mul_nonneg hu.le hD)
  change (u*D)*(2*N) ≤ (u*D)*T at hh
  nlinarith

lemma normalized_exponential_weight_lower {m : ℕ} (N u h₀ y₀ : ℝ) (h y : Fin m → ℝ)
    (hN : 0 < N) (hu : 0 < u) (hy : ∀ i, 0 ≤ y i) (hmin : ∀ i, h₀ ≤ h i)
    (htotal : 2*N ≤ y₀+∑ i, y i) :
    Real.exp (-N*h₀/u)*Real.exp (-(∑ i, (h i-h₀)*y i)/(2*u)) ≤
      Real.exp (-(N/u)*((h₀*y₀+∑ i, h i*y i)/(y₀+∑ i, y i))) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hh := normalized_weighted_energy_le N u h₀ y₀ h y hN hu hy hmin htotal
  convert! neg_le_neg hh using 1 <;> ring

#print axioms normalized_weighted_energy_le
#print axioms normalized_exponential_weight_lower
end SpectralRadiusUpperTail

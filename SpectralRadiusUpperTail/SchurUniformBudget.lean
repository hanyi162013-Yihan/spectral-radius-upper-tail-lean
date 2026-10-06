import SpectralRadiusUpperTail.SchurFiniteMomentBudget
import SpectralRadiusUpperTail.SchurSubexponential

namespace SpectralRadiusUpperTail
open Filter
open scoped BigOperators Topology

lemma schur_cuberoot_scaling (D : ℝ) (hD : 0 ≤ D) (k : ℕ) :
    (D*(k : ℝ)^2)^((1 : ℝ)/3) = D^((1 : ℝ)/3)*(k : ℝ)^((2 : ℝ)/3) := by
  rw [Real.mul_rpow hD (sq_nonneg _), ← Real.rpow_natCast_mul (Nat.cast_nonneg k) 2]
  norm_num

/-- The combinatorial Schur bound is uniform over all buffered radii
R>=eta, with a prefactor independent of the spectrum. -/
theorem schur_finite_moment_budget_uniform (n k : ℕ) (hn : 0 < n)
    (C η R : ℝ) (hC : 0 ≤ C) (hη : 0 < η) (hR : η ≤ R) :
    (∑ l ∈ Finset.range (k+1),
      (n.choose (l+1) : ℝ)*C^(l+1)*(4/(n : ℝ))^l*(k.choose l : ℝ)^2*R^(2*(k-l))) ≤
      C*(n : ℝ)*R^(2*k)*Real.exp
        (3*(4*C/η^2)^((1 : ℝ)/3)*(k : ℝ)^((2 : ℝ)/3)) := by
  have hR0 : 0 < R := hη.trans_le hR
  apply (schur_finite_moment_budget n k hn C R hC hR0).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have hD : 4*C/R^2 ≤ 4*C/η^2 := by
    exact div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hη)
      (pow_le_pow_left₀ hη.le hR 2)
  have hh := Real.rpow_le_rpow (show 0 ≤ (4*C/R^2)*(k : ℝ)^2 by positivity)
    (mul_le_mul_of_nonneg_right hD (sq_nonneg _)) (show (0 : ℝ) ≤ 1/3 by norm_num)
  rw [schur_cuberoot_scaling (4*C/η^2) (by positivity) k] at hh
  nlinarith

/-- At k/n -> alpha, the entire finite Schur counting loss is exp(o(n)),
uniformly in the buffered radius. -/
theorem schur_uniform_budget_subexponential (k : ℕ → ℕ) (α C η : ℝ)
    (hC : 0 < C) (hη : 0 < η)
    (hk : Tendsto (fun n => (k n : ℝ)/(n : ℝ)) atTop (𝓝 α))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ R : ℝ, η ≤ R →
      (∑ l ∈ Finset.range (k n+1),
        (n.choose (l+1) : ℝ)*C^(l+1)*(4/(n : ℝ))^l*((k n).choose l : ℝ)^2*R^(2*(k n-l))) ≤
        Real.exp ((n : ℝ)*ε)*R^(2*k n) := by
  have he := schur_prefactor_le_exp k α (2/3) (3*(4*C/η^2)^((1 : ℝ)/3)) C 1
    (by norm_num) (by norm_num) hC hk ε hε
  filter_upwards [he, eventually_gt_atTop 0] with n hn hn0 R hR
  have hb := schur_finite_moment_budget_uniform n (k n) hn0 C η R hC.le hη hR
  have hh := mul_le_mul_of_nonneg_right hn (pow_nonneg (hη.le.trans hR) (2*k n))
  simp only [pow_one] at hh
  apply hb.trans
  nlinarith [hh]

#print axioms schur_finite_moment_budget_uniform
#print axioms schur_uniform_budget_subexponential
end SpectralRadiusUpperTail

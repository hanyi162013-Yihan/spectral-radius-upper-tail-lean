import SpectralRadiusUpperTail.SchurPathCountBudget

namespace SpectralRadiusUpperTail
open scoped BigOperators

lemma schur_path_radius_factor (n k l : ℕ) (hn : 0 < n) (hlk : l ≤ k)
    (C R : ℝ) (hR : 0 < R) :
    C^(l+1)*(4/(n : ℝ))^l*R^(2*(k-l)) =
      C*R^(2*k)*((4*C/R^2)/(n : ℝ))^l := by
  have hpow : R^(2*k) = R^(2*(k-l))*(R^2)^l := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  rw [hpow]
  simp only [pow_succ, div_pow, mul_pow]
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  field_simp
  <;> ring

/-- All numerical Schur factors, including the radius and diagonal-block
constant, sum to a subexponential loss. The probabilistic path bound is
kept separate from this deterministic summation. -/
theorem schur_finite_moment_budget (n k : ℕ) (hn : 0 < n)
    (C R : ℝ) (hC : 0 ≤ C) (hR : 0 < R) :
    (∑ l ∈ Finset.range (k+1),
      (n.choose (l+1) : ℝ)*C^(l+1)*(4/(n : ℝ))^l*(k.choose l : ℝ)^2*R^(2*(k-l))) ≤
      C*(n : ℝ)*R^(2*k)*Real.exp (3*((4*C/R^2)*(k : ℝ)^2)^((1 : ℝ)/3)) := by
  have he : (∑ l ∈ Finset.range (k+1),
      (n.choose (l+1) : ℝ)*C^(l+1)*(4/(n : ℝ))^l*(k.choose l : ℝ)^2*R^(2*(k-l))) =
      C*R^(2*k)*(∑ l ∈ Finset.range (k+1),
        (n.choose (l+1) : ℝ)*((4*C/R^2)/(n : ℝ))^l*(k.choose l : ℝ)^2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    have hh := schur_path_radius_factor n k l hn (by simpa using Finset.mem_range.mp hl) C R hR
    calc
      _ = ((n.choose (l+1) : ℝ)*(k.choose l : ℝ)^2)*
          (C^(l+1)*(4/(n : ℝ))^l*R^(2*(k-l))) := by ring
      _ = _ := by rw [hh]; ring
  rw [he]
  have hh := mul_le_mul_of_nonneg_left
    (schur_path_count_sum_bound n k (k+1) hn (4*C/R^2) (by positivity))
    (show 0 ≤ C*R^(2*k) by positivity)
  calc
    _ ≤ C*R^(2*k)*((n : ℝ)*Real.exp (3*((4*C/R^2)*(k : ℝ)^2)^((1 : ℝ)/3))) := hh
    _ = _ := by ring

#print axioms schur_finite_moment_budget
end SpectralRadiusUpperTail

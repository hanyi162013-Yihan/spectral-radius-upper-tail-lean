import SpectralRadiusUpperTail.SchurFiniteFamilyBudget

namespace SpectralRadiusUpperTail
open scoped BigOperators

/-- A real Schur matrix has at most `n` diagonal blocks, because each
conjugate-pair block occupies two scalar coordinates. The path budget
continues to hold with a smaller number `N` of blocks. -/
theorem schur_finite_family_dimension_budget (N n k : ℕ) (hN : N ≤ n)
    (hn : 0 < n) (C R : ℝ) (hC : 0 ≤ C) (hR : 0 < R) :
    (∑ p : SchurFinitePathFamily N k,
      (k.choose p.1.val : ℝ)^2 *
        (C^(p.1.val+1)*(4/(n : ℝ))^p.1.val*R^(2*(k-p.1.val)))) ≤
      C*(n : ℝ)*R^(2*k)*Real.exp (3*((4*C/R^2)*(k : ℝ)^2)^((1 : ℝ)/3)) := by
  let f : ℕ → ℝ := fun l =>
    (k.choose l : ℝ)^2 * (C^(l+1)*(4/(n : ℝ))^l*R^(2*(k-l)))
  change (∑ p : SchurFinitePathFamily N k, f p.1.val) ≤ _
  rw [schurFinitePath_sum_by_length f]
  calc
    (∑ l : Fin (k+1), (N.choose (l.val+1) : ℝ)*f l.val) ≤
        ∑ l : Fin (k+1), (n.choose (l.val+1) : ℝ)*f l.val := by
      apply Finset.sum_le_sum
      intro l _
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast Nat.choose_le_choose (l.val+1) hN
      · dsimp [f]
        positivity
    _ = ∑ p : SchurFinitePathFamily n k, f p.1.val :=
      (schurFinitePath_sum_by_length f).symm
    _ ≤ _ := by
      dsimp [f]
      exact schur_finite_family_budget n k hn C R hC hR

#print axioms schur_finite_family_dimension_budget
end SpectralRadiusUpperTail

import SpectralRadiusUpperTail.SchurFinitePathFamily

namespace SpectralRadiusUpperTail
open scoped BigOperators

/-- Summing the numerical envelope over actual increasing block paths gives
the same subexponential budget as the abstract length count. -/
theorem schur_finite_family_budget (n k : ℕ) (hn : 0 < n)
    (C R : ℝ) (hC : 0 ≤ C) (hR : 0 < R) :
    (∑ p : SchurFinitePathFamily n k,
      (k.choose p.1.val : ℝ)^2 *
        (C^(p.1.val+1)*(4/(n : ℝ))^p.1.val*R^(2*(k-p.1.val)))) ≤
      C*(n : ℝ)*R^(2*k)*Real.exp (3*((4*C/R^2)*(k : ℝ)^2)^((1 : ℝ)/3)) := by
  have hsum := schurFinitePath_sum_by_length (N := n) (k := k)
    (fun l => (k.choose l : ℝ)^2 * (C^(l+1)*(4/(n : ℝ))^l*R^(2*(k-l))))
  rw [hsum]
  rw [Finset.sum_fin_eq_sum_range]
  have hh := schur_finite_moment_budget n k hn C R hC hR
  refine le_trans ?_ hh
  apply Finset.sum_le_sum
  intro l hl
  simp only [Finset.mem_range] at hl
  rw [dif_pos hl]
  simp only [Fin.val_mk]
  apply le_of_eq
  ring

#print axioms schur_finite_family_budget
end SpectralRadiusUpperTail

import SpectralRadiusUpperTail.RectangularColumnEnergy

namespace SpectralRadiusUpperTail
open WithLp
open scoped BigOperators Matrix Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma finite_matrix_column_norm_le (S : Matrix ι ι ℂ) (j : ι) :
    ‖toLp 2 (fun i => S i j)‖ ≤ ‖S‖ := by
  have hh := Matrix.l2_opNorm_mulVec S (PiLp.single 2 j (1 : ℂ))
  simp only [PiLp.ofLp_single,Matrix.mulVec_single_one,PiLp.norm_single,norm_one,mul_one] at hh
  exact hh

lemma finite_matrix_entry_norm_le (S : Matrix ι ι ℂ) (i j : ι) : ‖S i j‖ ≤ ‖S‖ := by
  exact (PiLp.norm_apply_le (toLp 2 (fun k => S k j)) i).trans
    (finite_matrix_column_norm_le S j)

#print axioms finite_matrix_column_norm_le
#print axioms finite_matrix_entry_norm_le
end SpectralRadiusUpperTail

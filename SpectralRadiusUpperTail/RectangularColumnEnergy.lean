import SpectralRadiusUpperTail.MatrixColumnNormalization

namespace SpectralRadiusUpperTail
open WithLp
open scoped BigOperators Matrix Matrix.Norms.L2Operator
variable {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma rectangular_column_norm_le (Q : Matrix (Fin n) ι ℂ) (j : ι) :
    ‖toLp 2 (fun i => Q i j)‖ ≤ ‖Q‖ := by
  have hh := Matrix.l2_opNorm_mulVec Q (PiLp.single 2 j (1 : ℂ))
  simp only [PiLp.ofLp_single,Matrix.mulVec_single_one,PiLp.norm_single,
    norm_one,mul_one] at hh
  exact hh

lemma rectangular_column_energy_le (Q : Matrix (Fin n) ι ℂ) (C : ℝ)
    (hC : 0 ≤ C) (hQ : ‖Q‖ ≤ C) (j : ι) :
    (∑ i, ‖Q i j‖^2) ≤ C^2 := by
  have hn := (rectangular_column_norm_le Q j).trans hQ
  have hs := pow_le_pow_left₀ (norm_nonneg (toLp 2 (fun i => Q i j))) hn 2
  rw [EuclideanSpace.norm_sq_eq] at hs
  exact hs

#print axioms rectangular_column_norm_le
#print axioms rectangular_column_energy_le
end SpectralRadiusUpperTail

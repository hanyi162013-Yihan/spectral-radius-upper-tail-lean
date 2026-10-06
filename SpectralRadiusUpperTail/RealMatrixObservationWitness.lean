import SpectralRadiusUpperTail.RealMatrixObservation
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Logic.Equiv.Fin.Rotate

namespace SpectralRadiusUpperTail
open scoped Matrix

theorem real_permMatrix_pow {ι : Type*} [Fintype ι] [DecidableEq ι]
    (σ : Equiv.Perm ι) (l : ℕ) :
    (σ.permMatrix ℝ)^l = (σ^l).permMatrix ℝ := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [pow_succ, ih, show σ^(l+1) = σ*σ^l from pow_succ' σ l,
      Matrix.permMatrix_mul]

theorem finRotate_pow_apply_coordinate (n : ℕ) (i k : Fin n) :
    ((finRotate n)^i.val) k = k+i := by
  change (finRotate n)^[i.val] k = _
  rw [← finCycle_eq_finRotate_iterate]
  rfl

/-- A cyclic permutation matrix witnesses nonvanishing of every
coordinate-observation determinant. -/
theorem realMatrixObservation_cycle (n : ℕ) (k : Fin n) :
    realMatrixObservation n ((finRotate n).permMatrix ℝ) k =
      (finCycle k).permMatrix ℝ := by
  ext i j
  change (((finRotate n).permMatrix ℝ)^i.val) k j = _
  rw [real_permMatrix_pow]
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_apply,
    finRotate_pow_apply_coordinate, finCycle_apply, add_comm]

theorem realMatrixObservation_cycle_det_ne_zero (n : ℕ) (k : Fin n) :
    (realMatrixObservation n ((finRotate n).permMatrix ℝ) k).det ≠ 0 := by
  rw [realMatrixObservation_cycle, Matrix.det_permutation]
  exact_mod_cast (Units.ne_zero (Equiv.Perm.sign (finCycle k)))

#print axioms real_permMatrix_pow
#print axioms finRotate_pow_apply_coordinate
#print axioms realMatrixObservation_cycle
#print axioms realMatrixObservation_cycle_det_ne_zero
end SpectralRadiusUpperTail

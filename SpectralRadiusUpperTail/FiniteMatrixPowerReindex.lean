import SpectralRadiusUpperTail.RectangularIsometryPower
import Mathlib.LinearAlgebra.Matrix.Reindex

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Frobenius BigOperators

theorem finite_frobenius_reindex_norm_sq {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (A : Matrix ι ι ℝ) : ‖Matrix.reindex e e A‖^2=‖A‖^2 := by
  rw [real_frobenius_norm_sq_finite,real_frobenius_norm_sq_finite]
  change (∑ i : κ, ∑ j : κ, (A (e.symm i) (e.symm j))^2)=∑ i : ι, ∑ j : ι, (A i j)^2
  rw [e.symm.sum_comp (fun i => ∑ j : κ, (A i (e.symm j))^2)]
  apply Finset.sum_congr rfl
  intro i _
  exact e.symm.sum_comp (fun j => (A i j)^2)

theorem finite_frobenius_reindex_power_norm_sq {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) (A : Matrix ι ι ℝ) (c : ℝ) (k : ℕ) :
    ‖(c • Matrix.reindex e e A)^k‖^2=‖(c • A)^k‖^2 := by
  have hs : c • Matrix.reindex e e A=Matrix.reindex e e (c • A) := rfl
  have hp : (Matrix.reindex e e (c • A))^k=Matrix.reindex e e ((c • A)^k) :=
    ((Matrix.reindexRingEquiv ℝ e).map_pow (c • A) k).symm
  rw [hs,hp,finite_frobenius_reindex_norm_sq]

#print axioms finite_frobenius_reindex_norm_sq
#print axioms finite_frobenius_reindex_power_norm_sq
end SpectralRadiusUpperTail

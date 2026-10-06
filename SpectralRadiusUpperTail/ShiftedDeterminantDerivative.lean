import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Analysis.Complex.Basic

namespace SpectralRadiusUpperTail
open scoped BigOperators

/-- Jacobi's formula along the scalar shift, before dividing by the determinant. -/
lemma shiftedDeterminant_hasDerivAt {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) :
    HasDerivAt (fun w : ℂ => Matrix.det (w • (1 : Matrix (Fin n) (Fin n) ℂ)-A))
      (Matrix.trace (Matrix.adjugate (z • (1 : Matrix (Fin n) (Fin n) ℂ)-A))) z := by
  let D : ContinuousMultilinearMap ℂ (fun _ : Fin n => Fin n → ℂ) ℂ :=
    { toMultilinearMap := Matrix.detRowAlternating.toMultilinearMap
      cont := continuous_id.matrix_det }
  let B : ℂ → Fin n → Fin n → ℂ := fun w i j => w * (1 : Matrix (Fin n) (Fin n) ℂ) i j-A i j
  let I : Fin n → Fin n → ℂ := fun i j => (1 : Matrix (Fin n) (Fin n) ℂ) i j
  have hcurve : HasDerivAt B I z := by
    convert! ((hasDerivAt_id z).smul_const I).sub_const (fun i j => A i j) using 1
    simp only [one_smul]
  have hh := (D.hasFDerivAt (B z)).comp_hasDerivAt z hcurve
  have he : (D.linearDeriv (B z)) I =
      Matrix.trace (Matrix.adjugate (z • (1 : Matrix (Fin n) (Fin n) ℂ)-A)) := by
    rw [ContinuousMultilinearMap.linearDeriv_apply]
    unfold Matrix.trace
    apply Finset.sum_congr rfl
    intro i _
    change Matrix.det (Matrix.of (Function.update (B z) i (I i))) = _
    rw [Matrix.diag_apply, Matrix.adjugate_apply]
    have hB : Matrix.of (B z) = z • (1 : Matrix (Fin n) (Fin n) ℂ)-A := by
      ext j k
      rfl
    have hI : I i = (Pi.single i 1 : Fin n → ℂ) := by
      ext j
      simp [I, Matrix.one_apply, Pi.single_apply, eq_comm]
    change (Matrix.updateRow (Matrix.of (B z)) i (I i)).det = _
    rw [hB, hI]
  rw [he] at hh
  convert! hh using 1

#print axioms shiftedDeterminant_hasDerivAt
end SpectralRadiusUpperTail

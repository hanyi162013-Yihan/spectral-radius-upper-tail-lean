import SpectralRadiusUpperTail.RealMatrixObservation
import Mathlib.LinearAlgebra.Matrix.Reindex

namespace SpectralRadiusUpperTail
open scoped Matrix

def realMatrixEigenvectorsHaveNonzeroCoordinates
    (ι : Type*) [Fintype ι] (A : Matrix ι ι ℝ) : Prop :=
  ∀ (v : ι → ℝ), v ≠ 0 → ∀ z : ℝ, A *ᵥ v = z • v → ∀ k : ι, v k ≠ 0

theorem realMatrixEigenvectorsHaveNonzeroCoordinates_reindex
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (A : Matrix ι ι ℝ)
    (hA : realMatrixEigenvectorsHaveNonzeroCoordinates ι A) :
    realMatrixEigenvectorsHaveNonzeroCoordinates κ (Matrix.reindex e e A) := by
  intro v hv z hAv k
  have hv' : v ∘ e ≠ 0 := by
    intro hzero
    apply hv
    funext i
    have hi := congrFun hzero (e.symm i)
    simpa only [Function.comp_apply, Equiv.apply_symm_apply, Pi.zero_apply] using hi
  have he : (Matrix.reindex e e A) *ᵥ v = (A *ᵥ (v ∘ e)) ∘ e.symm :=
    Matrix.submatrix_mulVec_equiv A v e.symm e.symm
  have hAv' : A *ᵥ (v ∘ e) = z • (v ∘ e) := by
    rw [he] at hAv
    funext i
    have hi := congrFun hAv (e i)
    simpa only [Function.comp_apply, Equiv.symm_apply_apply, Pi.smul_apply] using hi
  have hk := hA (v ∘ e) hv' z hAv' (e.symm k)
  simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hk

#print axioms realMatrixEigenvectorsHaveNonzeroCoordinates_reindex
end SpectralRadiusUpperTail

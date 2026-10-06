import SpectralRadiusUpperTail.RealSchurMixedSimpleSpectrum
import SpectralRadiusUpperTail.RealSchurMixedLocalIntegration
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory

private theorem finiteRealMatrix_simpleSpectrum_measurableSet
    (ι : Type*) [Fintype ι] [DecidableEq ι] :
    MeasurableSet {A : (ι × ι) → ℝ | (Matrix.of A.curry).charpoly.Separable} := by
  have hset : {A : (ι × ι) → ℝ | (Matrix.of A.curry).charpoly.Separable} =
      {A | MvPolynomial.eval A (finiteRealMatrixCollisionPolynomial ι) ≠ 0} := by
    ext A
    exact (finiteRealMatrixCollisionPolynomial_eval_ne_zero_iff ι A).symm
  rw [hset]
  exact ((measurableSet_singleton 0).preimage
    (finiteRealMatrixCollisionPolynomial ι).continuous_eval.measurable).compl

private theorem realSchurMixed_flat_symm_matrix
    {m : ℕ} (s : Fin m → ℕ) (y : RealSchurMixedTangent s) :
    Matrix.of ((realSchurMixedFlatEntryEquiv s).symm y).curry =
      (realSchurMixedEntryEquiv s).symm y := by
  simp [realSchurMixedFlatEntryEquiv, realMatrixEntryEquiv]
  ext i j
  rfl

/-- A mixed real-Schur coordinate matrix has simple characteristic roots
almost surely under the exact transported matrix-entry Lebesgue volume. -/
theorem realSchurMixed_charpoly_separable_ae_coordinateVolume
    {m : ℕ} (s : Fin m → ℕ) :
    ∀ᵐ y ∂realSchurMixedCoordinateVolume s,
      ((realSchurMixedEntryEquiv s).symm y).charpoly.Separable := by
  let f := realSchurMixedFlatEntryEquiv s
  let S : Set (RealSchurMixedTangent s) :=
    {y | ((realSchurMixedEntryEquiv s).symm y).charpoly.Separable}
  have hS : MeasurableSet S := by
    have heq : S = f.symm ⁻¹'
        {A : (RealSchurMixedCoord s × RealSchurMixedCoord s) → ℝ |
          (Matrix.of A.curry).charpoly.Separable} := by
      ext y
      change (((realSchurMixedEntryEquiv s).symm y).charpoly.Separable ↔
        (Matrix.of ((realSchurMixedFlatEntryEquiv s).symm y).curry).charpoly.Separable)
      rw [realSchurMixed_flat_symm_matrix]
    rw [heq]
    exact (finiteRealMatrix_simpleSpectrum_measurableSet
      (RealSchurMixedCoord s)).preimage
        f.symm.toContinuousLinearEquiv.continuous.measurable
  change ∀ᵐ y ∂Measure.map f
      (volume : Measure (RealSchurMixedCoord s × RealSchurMixedCoord s → ℝ)),
      y ∈ S
  apply (ae_map_iff f.toContinuousLinearEquiv.continuous.measurable.aemeasurable hS).mpr
  filter_upwards [finiteRealMatrix_charpoly_separable_ae_volume
    (RealSchurMixedCoord s)] with A hA
  change ((realSchurMixedEntryEquiv s).symm (f A)).charpoly.Separable
  have heq : ((realSchurMixedEntryEquiv s).symm (f A)) =
      Matrix.of A.curry := by
    simp [f, realSchurMixedFlatEntryEquiv, realMatrixEntryEquiv]
    ext i j
    rfl
  rwa [heq]

#print axioms realSchurMixed_charpoly_separable_ae_coordinateVolume
end SpectralRadiusUpperTail

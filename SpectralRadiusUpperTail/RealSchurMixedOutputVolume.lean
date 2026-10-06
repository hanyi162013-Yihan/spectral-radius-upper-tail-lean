import SpectralRadiusUpperTail.RealSchurMixedOrthogonalTransport
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped Matrix

/-- Orthogonal conjugation expressed in the ordinary flattened real
matrix-entry coordinates. -/
noncomputable def realMatrixOrthogonalEntryEquiv
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (Q : Matrix ι ι ℝ) (hQ : Qᵀ*Q=1) :
    (ι × ι → ℝ) ≃ₗ[ℝ] (ι × ι → ℝ) :=
  (realMatrixEntryEquiv ι).symm.trans
    ((realMatrixOrthogonalConjugationEquiv ι Q hQ).trans
      (realMatrixEntryEquiv ι))

theorem realMatrixOrthogonalEntryEquiv_det
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (Q : Matrix ι ι ℝ) (hQ : Qᵀ*Q=1) :
    LinearMap.det (realMatrixOrthogonalEntryEquiv ι Q hQ).toLinearMap = 1 := by
  have hc := LinearMap.det_conj
    (realMatrixOrthogonalConjugationEquiv ι Q hQ).toLinearMap
    (realMatrixEntryEquiv ι)
  change LinearMap.det
    ((realMatrixEntryEquiv ι).toLinearMap.comp
      ((realMatrixOrthogonalConjugationEquiv ι Q hQ).toLinearMap.comp
        (realMatrixEntryEquiv ι).symm.toLinearMap)) = 1
  rw [hc]
  exact realMatrixOrthogonalConjugationEquiv_det ι Q hQ

/-- Orthogonal conjugation preserves the standard Lebesgue measure on
all real matrix entries exactly. -/
theorem realMatrixOrthogonalEntryEquiv_measurePreserving
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (Q : Matrix ι ι ℝ) (hQ : Qᵀ*Q=1) :
    MeasurePreserving (realMatrixOrthogonalEntryEquiv ι Q hQ)
      (volume : Measure (ι × ι → ℝ)) volume := by
  let e := realMatrixOrthogonalEntryEquiv ι Q hQ
  have hd : LinearMap.det e.toLinearMap = 1 :=
    realMatrixOrthogonalEntryEquiv_det ι Q hQ
  have hm := Real.map_linearMap_volume_pi_eq_smul_volume_pi
    (f := e.toLinearMap) (by rw [hd]; exact one_ne_zero)
  refine ⟨e.toContinuousLinearEquiv.continuous.measurable, ?_⟩
  simpa [hd] using hm

#print axioms realMatrixOrthogonalEntryEquiv_measurePreserving
end SpectralRadiusUpperTail

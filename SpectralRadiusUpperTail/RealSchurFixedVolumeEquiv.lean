import SpectralRadiusUpperTail.RealSchurFixedCoordinateVolume
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped Matrix ENNReal

/-- A linear equivalence from the original `Fin n` entry array to the
mixed-Schur tangent coordinates. Its only nontrivial action is a finite
permutation of matrix entries. -/
noncomputable def realSchurFixedToMixedLinearEquiv
    {n : ℕ} {m : ℕ} {s : Fin m → ℕ}
    (e : Fin n ≃ RealSchurMixedCoord s) :
    ((Fin n × Fin n) → ℝ) ≃ₗ[ℝ] RealSchurMixedTangent s :=
  (realMatrixEntryEquiv (Fin n)).symm.trans
    ((Matrix.reindexLinearEquiv ℝ ℝ e e).trans
      (realSchurMixedEntryEquiv s))

theorem realSchurFixedToMixedLinearEquiv_apply
    {n : ℕ} {m : ℕ} {s : Fin m → ℕ}
    (e : Fin n ≃ RealSchurMixedCoord s)
    (x : (Fin n × Fin n) → ℝ) :
    realSchurFixedToMixedLinearEquiv e x =
      realSchurFixedToMixedTangent e x := by
  rw [realSchurFixedToMixedTangent_eq_reindex]
  rfl

theorem realSchurFixedToMixedLinearEquiv_measurePreserving
    {n : ℕ} {m : ℕ} {s : Fin m → ℕ}
    (e : Fin n ≃ RealSchurMixedCoord s) :
    MeasurePreserving (realSchurFixedToMixedLinearEquiv e)
      (volume : Measure ((Fin n × Fin n) → ℝ))
      (realSchurMixedCoordinateVolume s) := by
  have hfun : ⇑(realSchurFixedToMixedLinearEquiv e) =
      realSchurFixedToMixedTangent e :=
    funext (realSchurFixedToMixedLinearEquiv_apply e)
  rw [hfun]
  exact realSchurFixedToMixedTangent_measurePreserving e

/-- Transport a restricted nonnegative integral through the fixed-entry
permutation. No regularity assumption is needed on the integrand. -/
theorem realSchurFixedToMixedLinearEquiv_setLIntegral
    {n : ℕ} {m : ℕ} {s : Fin m → ℕ}
    (e : Fin n ≃ RealSchurMixedCoord s)
    (S : Set (RealSchurMixedTangent s)) (hS : MeasurableSet S)
    (g : RealSchurMixedTangent s → ℝ≥0∞) :
    ∫⁻ x in (realSchurFixedToMixedLinearEquiv e) ⁻¹' S,
        g (realSchurFixedToMixedLinearEquiv e x)
          ∂(volume : Measure ((Fin n × Fin n) → ℝ)) =
      ∫⁻ y in S, g y ∂realSchurMixedCoordinateVolume s := by
  let E := realSchurFixedToMixedLinearEquiv e
  have hEmb : MeasurableEmbedding E :=
    E.toContinuousLinearEquiv.toHomeomorph.measurableEmbedding
  have hmp : MeasurePreserving E
      (volume : Measure ((Fin n × Fin n) → ℝ))
      (realSchurMixedCoordinateVolume s) :=
    realSchurFixedToMixedLinearEquiv_measurePreserving e
  exact hmp.setLIntegral_comp_preimage_emb hEmb g S

#print axioms realSchurFixedToMixedLinearEquiv_setLIntegral
end SpectralRadiusUpperTail

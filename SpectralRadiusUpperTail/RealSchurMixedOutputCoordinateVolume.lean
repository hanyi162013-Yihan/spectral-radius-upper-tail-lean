import SpectralRadiusUpperTail.RealSchurMixedOutputVolume
import SpectralRadiusUpperTail.RealSchurMixedLocalIntegration
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped Matrix

/-- Orthogonal output conjugation transported to the fixed mixed-Schur
lower/upper matrix-entry coordinates. -/
noncomputable def realSchurMixedOutputCoordinateEquiv
    {m : ℕ} (s : Fin m → ℕ)
    (Q : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hQ : Qᵀ*Q=1) :
    RealSchurMixedTangent s ≃ₗ[ℝ] RealSchurMixedTangent s :=
  (realSchurMixedFlatEntryEquiv s).symm.trans
    ((realMatrixOrthogonalEntryEquiv (RealSchurMixedCoord s) Q hQ).trans
      (realSchurMixedFlatEntryEquiv s))

theorem realSchurMixedOutputCoordinateEquiv_comp_flat
    {m : ℕ} (s : Fin m → ℕ)
    (Q : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hQ : Qᵀ*Q=1)
    (f : RealSchurMixedCoord s × RealSchurMixedCoord s → ℝ) :
    realSchurMixedOutputCoordinateEquiv s Q hQ
        (realSchurMixedFlatEntryEquiv s f) =
      realSchurMixedFlatEntryEquiv s
        (realMatrixOrthogonalEntryEquiv (RealSchurMixedCoord s) Q hQ f) := by
  simp [realSchurMixedOutputCoordinateEquiv]

/-- Orthogonal rotation of the output matrix preserves the actual
coordinate volume used in the mixed real-Schur local integral. -/
theorem realSchurMixedOutputCoordinateEquiv_measurePreserving
    {m : ℕ} (s : Fin m → ℕ)
    (Q : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hQ : Qᵀ*Q=1) :
    MeasurePreserving (realSchurMixedOutputCoordinateEquiv s Q hQ)
      (realSchurMixedCoordinateVolume s)
      (realSchurMixedCoordinateVolume s) := by
  let E := realSchurMixedOutputCoordinateEquiv s Q hQ
  let L := realSchurMixedFlatEntryEquiv s
  let R := realMatrixOrthogonalEntryEquiv (RealSchurMixedCoord s) Q hQ
  have hE : Measurable E := E.toContinuousLinearEquiv.continuous.measurable
  have hL : Measurable L := L.toContinuousLinearEquiv.continuous.measurable
  have hR : Measurable R := R.toContinuousLinearEquiv.continuous.measurable
  have hRmap : Measure.map R (volume : Measure (RealSchurMixedCoord s ×
      RealSchurMixedCoord s → ℝ)) = volume :=
    (realMatrixOrthogonalEntryEquiv_measurePreserving
      (RealSchurMixedCoord s) Q hQ).map_eq
  refine ⟨hE, ?_⟩
  change Measure.map E (Measure.map L volume) = Measure.map L volume
  rw [Measure.map_map hE hL]
  have hcomp : E ∘ L = L ∘ R := by
    funext f
    exact realSchurMixedOutputCoordinateEquiv_comp_flat s Q hQ f
  rw [hcomp, ← Measure.map_map hL hR, hRmap]

#print axioms realSchurMixedOutputCoordinateEquiv_measurePreserving
end SpectralRadiusUpperTail

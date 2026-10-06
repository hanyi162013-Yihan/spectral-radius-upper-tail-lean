import SpectralRadiusUpperTail.RealSchurMixedEntryProductVolume
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory

/-- Read the fixed lower/diagonal/strict-upper entry arrays from a
real-Schur tangent parameter. -/
noncomputable def realSchurMixedTangentEntries
    {m : ℕ} (s : Fin m → ℕ)
    (x : RealSchurMixedTangent s) :
      (RealSchurMixedOrbitIndex s → ℝ) ×
        ((RealSchurMixedDiagonalEntry s → ℝ) ×
          (RealSchurMixedStrictUpperEntry s → ℝ)) :=
  (x.1, realSchurMixedUpperEntryEquiv s x.2)

theorem realSchurMixedTangentEntries_measurable
    {m : ℕ} (s : Fin m → ℕ) :
    Measurable (realSchurMixedTangentEntries s) := by
  have h : Continuous (realSchurMixedTangentEntries s) :=
    continuous_fst.prodMk
      ((realSchurMixedUpperEntryEquiv s).toContinuousLinearEquiv.continuous.comp
        continuous_snd)
  exact h.measurable

theorem realSchurMixedFlatEntry_lower_coordinates
    {m : ℕ} (s : Fin m → ℕ)
    (f : RealSchurMixedCoord s × RealSchurMixedCoord s → ℝ) :
    (realSchurMixedFlatEntryEquiv s f).1 =
      (fun p : RealSchurMixedOrbitIndex s =>
        f (realSchurMixedLowerEntryEquiv s p).val) := by
  rfl

/-- The abstract tangent entry map is the concrete measurable entry
partition after the fixed matrix-entry equivalence. -/
theorem realSchurMixedTangentEntries_comp_flat
    {m : ℕ} (s : Fin m → ℕ)
    (f : RealSchurMixedCoord s × RealSchurMixedCoord s → ℝ) :
    realSchurMixedTangentEntries s (realSchurMixedFlatEntryEquiv s f) =
      realSchurMixedEntryProductEquiv s f := by
  rw [realSchurMixedEntryProductEquiv_apply]
  apply Prod.ext
  · exact realSchurMixedFlatEntry_lower_coordinates s f
  · exact realSchurMixedFlatEntry_upper_coordinates s f

/-- The parameter volume used in the local Schur change of variables is
exactly the product of independent lower, diagonal, and upper entry volumes. -/
theorem realSchurMixedCoordinateVolume_entryProduct
    {m : ℕ} (s : Fin m → ℕ) :
    Measure.map (realSchurMixedTangentEntries s)
      (realSchurMixedCoordinateVolume s) = volume := by
  have hflat : Measurable (realSchurMixedFlatEntryEquiv s) :=
    (realSchurMixedFlatEntryEquiv s).toContinuousLinearEquiv.continuous.measurable
  rw [realSchurMixedCoordinateVolume,
    Measure.map_map (realSchurMixedTangentEntries_measurable s) hflat]
  have heq : (realSchurMixedTangentEntries s ∘
        realSchurMixedFlatEntryEquiv s) =
        realSchurMixedEntryProductEquiv s := by
    funext f
    exact realSchurMixedTangentEntries_comp_flat s f
  rw [heq]
  exact (realSchurMixedEntryProductEquiv_measurePreserving s).map_eq

#print axioms realSchurMixedCoordinateVolume_entryProduct
end SpectralRadiusUpperTail

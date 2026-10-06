import SpectralRadiusUpperTail.RealSchurFixedAtlasSequence
import SpectralRadiusUpperTail.RealSchurMixedLocalIntegration
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped Matrix

/-- Reorder the entries of a fixed `Fin n` matrix into the coordinates of
one mixed real-Schur block shape. -/
noncomputable def realSchurFixedFlatReindex
    {n : ℕ} {m : ℕ} {s : Fin m → ℕ}
    (e : Fin n ≃ RealSchurMixedCoord s) :
    ((Fin n × Fin n) → ℝ) ≃ᵐ
      ((RealSchurMixedCoord s × RealSchurMixedCoord s) → ℝ) :=
  MeasurableEquiv.piCongrLeft
    (fun _ : RealSchurMixedCoord s × RealSchurMixedCoord s => ℝ)
    (Equiv.prodCongr e e)

/-- Entry reindexing preserves Lebesgue volume without a Jacobian factor. -/
theorem realSchurFixedFlatReindex_measurePreserving
    {n : ℕ} {m : ℕ} {s : Fin m → ℕ}
    (e : Fin n ≃ RealSchurMixedCoord s) :
    MeasurePreserving (realSchurFixedFlatReindex e)
      (volume : Measure ((Fin n × Fin n) → ℝ))
      (volume : Measure ((RealSchurMixedCoord s × RealSchurMixedCoord s) → ℝ)) := by
  exact volume_measurePreserving_piCongrLeft _ _

theorem realSchurFixedFlatReindex_apply
    {n : ℕ} {m : ℕ} {s : Fin m → ℕ}
    (e : Fin n ≃ RealSchurMixedCoord s)
    (x : (Fin n × Fin n) → ℝ)
    (p : RealSchurMixedCoord s × RealSchurMixedCoord s) :
    realSchurFixedFlatReindex e x p =
      x (e.symm p.1, e.symm p.2) := by
  rcases p with ⟨i,j⟩
  have h := MeasurableEquiv.piCongrLeft_apply_apply
    (β := fun _ => ℝ) (Equiv.prodCongr e e) x
    (e.symm i, e.symm j)
  simpa [realSchurFixedFlatReindex, Equiv.prodCongr] using h

/-- The mixed tangent coordinate map, starting from the actual fixed
matrix-entry array. -/
noncomputable def realSchurFixedToMixedTangent
    {n : ℕ} {m : ℕ} {s : Fin m → ℕ}
    (e : Fin n ≃ RealSchurMixedCoord s)
    (x : (Fin n × Fin n) → ℝ) : RealSchurMixedTangent s :=
  realSchurMixedFlatEntryEquiv s (realSchurFixedFlatReindex e x)

theorem realSchurFixedToMixedTangent_eq_reindex
    {n : ℕ} {m : ℕ} {s : Fin m → ℕ}
    (e : Fin n ≃ RealSchurMixedCoord s)
    (x : (Fin n × Fin n) → ℝ) :
    realSchurFixedToMixedTangent e x =
      realSchurMixedEntryEquiv s
        (Matrix.reindex e e (Matrix.of x.curry)) := by
  change (realSchurMixedEntryEquiv s)
    ((realMatrixEntryEquiv (RealSchurMixedCoord s)).symm
      (realSchurFixedFlatReindex e x)) = _
  congr 1
  ext i j
  exact realSchurFixedFlatReindex_apply e x (i,j)

/-- The fixed-array entry volume becomes exactly the coordinate Haar
measure already used in the local Schur Jacobian theorem. -/
theorem realSchurFixedToMixedTangent_map_volume
    {n : ℕ} {m : ℕ} {s : Fin m → ℕ}
    (e : Fin n ≃ RealSchurMixedCoord s) :
    Measure.map (realSchurFixedToMixedTangent e)
      (volume : Measure ((Fin n × Fin n) → ℝ)) =
        realSchurMixedCoordinateVolume s := by
  have hflat : Measurable (realSchurMixedFlatEntryEquiv s) :=
    (realSchurMixedFlatEntryEquiv s).continuous_of_finiteDimensional.measurable
  have hperm := realSchurFixedFlatReindex_measurePreserving e
  change Measure.map
    ((realSchurMixedFlatEntryEquiv s) ∘ (realSchurFixedFlatReindex e)) volume = _
  rw [← Measure.map_map hflat (realSchurFixedFlatReindex e).measurable,
    hperm.map_eq]
  rfl

theorem realSchurFixedToMixedTangent_measurePreserving
    {n : ℕ} {m : ℕ} {s : Fin m → ℕ}
    (e : Fin n ≃ RealSchurMixedCoord s) :
    MeasurePreserving (realSchurFixedToMixedTangent e)
      (volume : Measure ((Fin n × Fin n) → ℝ))
      (realSchurMixedCoordinateVolume s) := by
  refine ⟨?_, realSchurFixedToMixedTangent_map_volume e⟩
  exact (realSchurMixedFlatEntryEquiv s).continuous_of_finiteDimensional.measurable.comp
    (realSchurFixedFlatReindex e).measurable

#print axioms realSchurFixedToMixedTangent_map_volume
end SpectralRadiusUpperTail

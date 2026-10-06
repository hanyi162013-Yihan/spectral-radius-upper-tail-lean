import SpectralRadiusUpperTail.RealSchurMixedEntryPartition
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory

/-- Reorder every real matrix entry into lower, diagonal-block, and
strictly-upper-block coordinate arrays. -/
noncomputable def realSchurMixedEntryProductEquiv
    {m : ℕ} (s : Fin m → ℕ) :
    (RealSchurMixedCoord s × RealSchurMixedCoord s → ℝ) ≃ᵐ
      ((RealSchurMixedOrbitIndex s → ℝ) ×
        ((RealSchurMixedDiagonalEntry s → ℝ) ×
          (RealSchurMixedStrictUpperEntry s → ℝ))) := by
  classical
  let e₁ := MeasurableEquiv.piEquivPiSubtypeProd
    (fun _ : RealSchurMixedCoord s × RealSchurMixedCoord s => ℝ)
    (fun p => p.2.1 < p.1.1)
  let e₂ := MeasurableEquiv.piEquivPiSubtypeProd
    (fun _ : RealSchurMixedNonlowerEntry s => ℝ)
    (fun p => p.1.1.1 = p.1.2.1)
  let e₃ := MeasurableEquiv.prodCongr
    (MeasurableEquiv.refl (RealSchurMixedLowerEntry s → ℝ)) e₂
  let e₄ := MeasurableEquiv.prodCongr
    (MeasurableEquiv.piCongrLeft (fun _ : RealSchurMixedLowerEntry s => ℝ)
      (realSchurMixedLowerEntryEquiv s)).symm
    (MeasurableEquiv.prodCongr
      (MeasurableEquiv.piCongrLeft
        (fun _ : RealSchurMixedNonlowerDiagonalEntry s => ℝ)
        (realSchurMixedDiagonalPartitionEquiv s)).symm
      (MeasurableEquiv.piCongrLeft
        (fun _ : RealSchurMixedNonlowerStrictEntry s => ℝ)
        (realSchurMixedStrictPartitionEquiv s)).symm)
  exact e₁.trans (e₃.trans e₄)

/-- Entry reordering carries the full matrix-entry volume exactly to the
three independent product volumes. -/
theorem realSchurMixedEntryProductEquiv_measurePreserving
    {m : ℕ} (s : Fin m → ℕ) :
    MeasurePreserving (realSchurMixedEntryProductEquiv s) := by
  classical
  let e₁ := MeasurableEquiv.piEquivPiSubtypeProd
    (fun _ : RealSchurMixedCoord s × RealSchurMixedCoord s => ℝ)
    (fun p => p.2.1 < p.1.1)
  let e₂ := MeasurableEquiv.piEquivPiSubtypeProd
    (fun _ : RealSchurMixedNonlowerEntry s => ℝ)
    (fun p => p.1.1.1 = p.1.2.1)
  let e₃ := MeasurableEquiv.prodCongr
    (MeasurableEquiv.refl (RealSchurMixedLowerEntry s → ℝ)) e₂
  let e₄ := MeasurableEquiv.prodCongr
    (MeasurableEquiv.piCongrLeft (fun _ : RealSchurMixedLowerEntry s => ℝ)
      (realSchurMixedLowerEntryEquiv s)).symm
    (MeasurableEquiv.prodCongr
      (MeasurableEquiv.piCongrLeft
        (fun _ : RealSchurMixedNonlowerDiagonalEntry s => ℝ)
        (realSchurMixedDiagonalPartitionEquiv s)).symm
      (MeasurableEquiv.piCongrLeft
        (fun _ : RealSchurMixedNonlowerStrictEntry s => ℝ)
        (realSchurMixedStrictPartitionEquiv s)).symm)
  change MeasurePreserving (e₁.trans (e₃.trans e₄))
  have h₁ : MeasurePreserving e₁ :=
    volume_preserving_piEquivPiSubtypeProd _ _
  have h₂ : MeasurePreserving e₂ :=
    volume_preserving_piEquivPiSubtypeProd _ _
  have h₃ : MeasurePreserving e₃ :=
    (MeasurePreserving.id (volume : Measure (RealSchurMixedLowerEntry s → ℝ))).prod h₂
  have h₄l : MeasurePreserving
      (MeasurableEquiv.piCongrLeft (fun _ : RealSchurMixedLowerEntry s => ℝ)
        (realSchurMixedLowerEntryEquiv s)).symm :=
    (volume_measurePreserving_piCongrLeft _ _).symm
  have h₄d : MeasurePreserving
      (MeasurableEquiv.piCongrLeft
        (fun _ : RealSchurMixedNonlowerDiagonalEntry s => ℝ)
        (realSchurMixedDiagonalPartitionEquiv s)).symm :=
    (volume_measurePreserving_piCongrLeft _ _).symm
  have h₄u : MeasurePreserving
      (MeasurableEquiv.piCongrLeft
        (fun _ : RealSchurMixedNonlowerStrictEntry s => ℝ)
        (realSchurMixedStrictPartitionEquiv s)).symm :=
    (volume_measurePreserving_piCongrLeft _ _).symm
  have h₄ : MeasurePreserving e₄ :=
    h₄l.prod (h₄d.prod h₄u)
  exact h₄.comp h₃ |>.comp h₁

/-- The three output arrays are exactly the corresponding original entries. -/
theorem realSchurMixedEntryProductEquiv_apply
    {m : ℕ} (s : Fin m → ℕ)
    (f : RealSchurMixedCoord s × RealSchurMixedCoord s → ℝ) :
    realSchurMixedEntryProductEquiv s f =
      ((fun p : RealSchurMixedOrbitIndex s =>
          f (realSchurMixedLowerEntryEquiv s p).val),
       ((fun p : RealSchurMixedDiagonalEntry s => f p.val),
        (fun p : RealSchurMixedStrictUpperEntry s => f p.val))) := by
  rfl

#print axioms realSchurMixedEntryProductEquiv
end SpectralRadiusUpperTail

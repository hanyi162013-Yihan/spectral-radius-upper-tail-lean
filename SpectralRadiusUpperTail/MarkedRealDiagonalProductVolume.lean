import SpectralRadiusUpperTail.MarkedRealDiagonalCoordinates
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory

/-- Split diagonal entries into a real scalar and a complementary
matrix, without any Jacobian factor. -/
noncomputable def markedRealDiagonalProductEquiv (m : ℕ) :
    (RealSchurMixedDiagonalEntry (markedRealTwoBlockSizes m) → ℝ) ≃ᵐ
      (ℝ × ((Fin m × Fin m) → ℝ)) :=
  (MeasurableEquiv.piCongrLeft
    (fun _ : RealSchurMixedDiagonalEntry (markedRealTwoBlockSizes m) => ℝ)
    (markedRealDiagonalEntryEquiv m)).symm |>.trans
  ((MeasurableEquiv.sumPiEquivProdPi
    (fun _ : Unit ⊕ (Fin m × Fin m) => ℝ)).trans
      (MeasurableEquiv.prodCongr
        (MeasurableEquiv.funUnique Unit ℝ)
        (MeasurableEquiv.refl ((Fin m × Fin m) → ℝ))))

theorem markedRealDiagonalProductEquiv_fst (m : ℕ)
    (d : RealSchurMixedDiagonalEntry (markedRealTwoBlockSizes m) → ℝ) :
    (markedRealDiagonalProductEquiv m d).1 =
      d (markedRealScalarDiagonalEntry m) := by
  rfl

theorem markedRealDiagonalProductEquiv_snd (m : ℕ)
    (d : RealSchurMixedDiagonalEntry (markedRealTwoBlockSizes m) → ℝ)
    (i j : Fin m) :
    (markedRealDiagonalProductEquiv m d).2 (i,j) =
      d (markedRealComplementDiagonalEntry m i j) := by
  rfl

theorem markedRealDiagonalProductEquiv_measurePreserving (m : ℕ) :
    MeasurePreserving (markedRealDiagonalProductEquiv m) := by
  let e₁ := (MeasurableEquiv.piCongrLeft
    (fun _ : RealSchurMixedDiagonalEntry (markedRealTwoBlockSizes m) => ℝ)
    (markedRealDiagonalEntryEquiv m)).symm
  let e₂ := MeasurableEquiv.sumPiEquivProdPi
    (fun _ : Unit ⊕ (Fin m × Fin m) => ℝ)
  let e₃ := MeasurableEquiv.prodCongr
    (MeasurableEquiv.funUnique Unit ℝ)
    (MeasurableEquiv.refl ((Fin m × Fin m) → ℝ))
  change MeasurePreserving (e₁.trans (e₂.trans e₃))
  have h₁ : MeasurePreserving e₁ :=
    (volume_measurePreserving_piCongrLeft _ _).symm
  have h₂ : MeasurePreserving e₂ :=
    volume_measurePreserving_sumPiEquivProdPi _
  have h₃ : MeasurePreserving e₃ :=
    (volume_preserving_funUnique Unit ℝ).prod
      (MeasurePreserving.id (volume : Measure ((Fin m × Fin m) → ℝ)))
  exact (h₃.comp h₂).comp h₁

#print axioms markedRealDiagonalProductEquiv_measurePreserving
end SpectralRadiusUpperTail

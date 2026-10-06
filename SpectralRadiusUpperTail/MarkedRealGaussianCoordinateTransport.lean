import SpectralRadiusUpperTail.GaussianMixedCoordinateLaw
import SpectralRadiusUpperTail.GaussianMatrixReindexLaw
import SpectralRadiusUpperTail.MarkedRealTwoBlockOrbit
import SpectralRadiusUpperTail.MarkedRealEigenlineBasis
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped Matrix

/-- Fixed identification of the ordinary matrix indices with the
marked 1 plus complementary m block indices. -/
noncomputable def markedRealIndexEquiv (m : ℕ) :
    Fin (m+1) ≃ RealSchurMixedCoord (markedRealTwoBlockSizes m) :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_fin, markedRealTwoBlock_card])

/-- The measurable coordinate equivalence taking an ordinary real
matrix array into the mixed Schur entry-coordinate space. -/
noncomputable def markedRealGaussianEntryEquiv (m : ℕ) :
    ((Fin (m+1) × Fin (m+1)) → ℝ) ≃ᵐ
      RealSchurMixedTangent (markedRealTwoBlockSizes m) :=
  (MeasurableEquiv.piCongrLeft
    (fun _ : RealSchurMixedCoord (markedRealTwoBlockSizes m) ×
      RealSchurMixedCoord (markedRealTwoBlockSizes m) => ℝ)
    (Equiv.prodCongr (markedRealIndexEquiv m) (markedRealIndexEquiv m))).trans
      ((realSchurMixedFlatEntryEquiv
        (markedRealTwoBlockSizes m)).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv)

theorem markedRealGaussianEntryEquiv_matrix
    (m : ℕ) (a : (Fin (m+1) × Fin (m+1)) → ℝ) :
    (realSchurMixedEntryEquiv (markedRealTwoBlockSizes m)).symm
      (markedRealGaussianEntryEquiv m a) =
        Matrix.reindex (markedRealIndexEquiv m)
          (markedRealIndexEquiv m) (Matrix.of a.curry) := by
  ext i j
  simp [markedRealGaussianEntryEquiv, realSchurMixedFlatEntryEquiv,
    realMatrixEntryEquiv, Matrix.reindex_apply]
  change (MeasurableEquiv.piCongrLeft
    (fun _ : RealSchurMixedCoord (markedRealTwoBlockSizes m) ×
      RealSchurMixedCoord (markedRealTwoBlockSizes m) => ℝ)
    (Equiv.prodCongr (markedRealIndexEquiv m)
      (markedRealIndexEquiv m)) a) (i,j) =
        a ((markedRealIndexEquiv m).symm i,
          (markedRealIndexEquiv m).symm j)
  let e := markedRealIndexEquiv m
  let p := Equiv.prodCongr e e
  have hv := MeasurableEquiv.piCongrLeft_apply_apply
    (β := fun _ : RealSchurMixedCoord (markedRealTwoBlockSizes m) ×
      RealSchurMixedCoord (markedRealTwoBlockSizes m) => ℝ)
    p a (p.symm (i,j))
  simpa [p, e, Equiv.prodCongr] using hv

/-- Under the actual iid Gaussian law, the coordinate equivalence has
exactly the transported mixed-array Gaussian distribution. -/
theorem gaussianMatrixLaw_map_markedRealGaussianEntryEquiv
    (m : ℕ) :
    (gaussianMatrixLaw (m+1)).map
      (markedRealGaussianEntryEquiv m) =
        (Measure.pi
          (fun _ : RealSchurMixedCoord (markedRealTwoBlockSizes m) ×
            RealSchurMixedCoord (markedRealTwoBlockSizes m) =>
              standardNormal)).map
          (realSchurMixedFlatEntryEquiv (markedRealTwoBlockSizes m)) := by
  let e := markedRealIndexEquiv m
  let p := Equiv.prodCongr e e
  let R : ((Fin (m+1) × Fin (m+1)) → ℝ) ≃ᵐ
      ((RealSchurMixedCoord (markedRealTwoBlockSizes m) ×
        RealSchurMixedCoord (markedRealTwoBlockSizes m)) → ℝ) :=
    MeasurableEquiv.piCongrLeft
      (fun _ : RealSchurMixedCoord (markedRealTwoBlockSizes m) ×
        RealSchurMixedCoord (markedRealTwoBlockSizes m) => ℝ)
      p
  have hR : (R : ((Fin (m+1) × Fin (m+1)) → ℝ) →
      ((RealSchurMixedCoord (markedRealTwoBlockSizes m) ×
        RealSchurMixedCoord (markedRealTwoBlockSizes m)) → ℝ)) =
      (fun a ij => a (e.symm ij.1, e.symm ij.2)) := by
    funext a ij
    have hv := MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : RealSchurMixedCoord (markedRealTwoBlockSizes m) ×
        RealSchurMixedCoord (markedRealTwoBlockSizes m) => ℝ)
      p a (p.symm ij)
    change R a ij = a (p.symm ij)
    simpa only [Equiv.apply_symm_apply] using hv
  have hF : (markedRealGaussianEntryEquiv m :
      ((Fin (m+1) × Fin (m+1)) → ℝ) →
        RealSchurMixedTangent (markedRealTwoBlockSizes m)) =
      (realSchurMixedFlatEntryEquiv (markedRealTwoBlockSizes m)) ∘ R := rfl
  rw [hF]
  have hmeasF : Measurable
      (realSchurMixedFlatEntryEquiv (markedRealTwoBlockSizes m)) :=
    (realSchurMixedFlatEntryEquiv
      (markedRealTwoBlockSizes m)).toContinuousLinearEquiv.continuous.measurable
  calc
    Measure.map ((realSchurMixedFlatEntryEquiv
      (markedRealTwoBlockSizes m)) ∘ R)
        (gaussianMatrixLaw (m+1)) =
      Measure.map (realSchurMixedFlatEntryEquiv
        (markedRealTwoBlockSizes m))
        ((gaussianMatrixLaw (m+1)).map R) :=
      (Measure.map_map hmeasF R.measurable).symm
    _ = _ := by rw [hR, gaussianMatrixLaw_map_reindex e]

#print axioms markedRealGaussianEntryEquiv_matrix
#print axioms gaussianMatrixLaw_map_markedRealGaussianEntryEquiv
end SpectralRadiusUpperTail

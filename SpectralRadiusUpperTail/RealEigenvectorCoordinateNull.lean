import SpectralRadiusUpperTail.RealMatrixObservationPolynomial
import SpectralRadiusUpperTail.RealEigenvectorCoordinateReindex
import SpectralRadiusUpperTail.MarkedRealGaussianCoordinateTransport

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped Matrix

/-- The coordinate-zero eigenvector exception is Lebesgue null on any
finite real matrix index type, with a fixed enumeration. -/
theorem realMatrix_eigenvectors_nonzero_coordinates_ae_volume
    {n : ℕ} {ι : Type*} [Fintype ι] (e : Fin n ≃ ι) :
    ∀ᵐ a : (ι × ι) → ℝ,
      realMatrixEigenvectorsHaveNonzeroCoordinates ι (Matrix.of a.curry) := by
  let p := Equiv.prodCongr e e
  let R := MeasurableEquiv.piCongrLeft (fun _ : ι × ι => ℝ) p
  have hR : MeasurePreserving R volume volume :=
    volume_measurePreserving_piCongrLeft _ _
  rw [← hR.map_eq]
  apply R.measurableEmbedding.ae_map_iff.mpr
  filter_upwards [realMatrixObservation_det_ne_zero_ae_volume n] with a ha
  have hgood : realMatrixEigenvectorsHaveNonzeroCoordinates (Fin n) (Matrix.of a.curry) := by
    intro v hv z hAv k
    exact realMatrix_eigenvector_coordinate_ne_zero n _ k (ha k) v hv z hAv
  have hmat : Matrix.of (R a).curry = Matrix.reindex e e (Matrix.of a.curry) := by
    ext i j
    change R a (i,j) = a (e.symm i,e.symm j)
    have hi := MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : ι × ι => ℝ) p a (p.symm (i,j))
    simpa [R, p, Equiv.prodCongr] using hi
  rw [hmat]
  exact realMatrixEigenvectorsHaveNonzeroCoordinates_reindex e _ hgood

/-- In the actual Schur coordinate volume, almost every matrix has no
real eigenline on the equator of the explicit hemisphere chart. -/
theorem markedReal_eigenvectors_nonzero_coordinates_ae
    (m : ℕ) :
    ∀ᵐ y ∂realSchurMixedCoordinateVolume (markedRealTwoBlockSizes m),
      realMatrixEigenvectorsHaveNonzeroCoordinates
        (RealSchurMixedCoord (markedRealTwoBlockSizes m))
        ((realSchurMixedEntryEquiv (markedRealTwoBlockSizes m)).symm y) := by
  unfold realSchurMixedCoordinateVolume
  apply (realSchurMixedFlatEntryEquiv (markedRealTwoBlockSizes m)).toContinuousLinearEquiv.toHomeomorph.measurableEmbedding.ae_map_iff.mpr
  filter_upwards [realMatrix_eigenvectors_nonzero_coordinates_ae_volume
    (markedRealIndexEquiv m)] with a ha
  change realMatrixEigenvectorsHaveNonzeroCoordinates _
    ((realSchurMixedEntryEquiv (markedRealTwoBlockSizes m)).symm
      (realSchurMixedEntryEquiv (markedRealTwoBlockSizes m)
        ((realMatrixEntryEquiv _).symm a)))
  rw [LinearEquiv.symm_apply_apply]
  exact ha

#print axioms realMatrix_eigenvectors_nonzero_coordinates_ae_volume
#print axioms markedReal_eigenvectors_nonzero_coordinates_ae
end SpectralRadiusUpperTail

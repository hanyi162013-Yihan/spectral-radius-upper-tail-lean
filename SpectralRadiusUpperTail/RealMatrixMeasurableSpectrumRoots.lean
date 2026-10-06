import SpectralRadiusUpperTail.RealGaussianMeasurableRoots
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

/-- The measurable complex-Schur labels describe the roots of every
simple-spectrum real matrix, pointwise rather than merely Gaussian-almost
everywhere. -/
theorem realMatrixMeasurableRawSpectrum_roots_of_separable
    (n : ℕ) (x : (Fin n × Fin n) → ℝ)
    (hx : (Matrix.of x.curry).charpoly.Separable) :
    ((Matrix.of x.curry).map Complex.ofRealHom).charpoly.roots =
      (Finset.univ : Finset (Fin n)).val.map
        (realGaussianMeasurableRawSpectrum n x) := by
  let A : Matrix (Fin n) (Fin n) ℂ :=
    (Matrix.of x.curry).map Complex.ofRealHom
  have hsep : A.charpoly.Separable := by
    dsimp [A]
    rw [Matrix.charpoly_map]
    exact (Polynomial.separable_map (algebraMap ℝ ℂ)).mpr hx
  have hmem := Ginibre.entrySplit_simple_mem_iUnion_schurDisjointEntryImage
    A hsep
  have hflat : Ginibre.schurFlatEntryMeasurableEquiv n
      (fun ij => (x ij : ℂ)) = Ginibre.schurEntrySplit n A := by
    rw [Ginibre.schurFlatEntryMeasurableEquiv_apply]
    congr 1
  have hlabels : realGaussianMeasurableRawSpectrum n x =
      Ginibre.schurSpectrum A := by
    change (Classical.choose
      (Ginibre.exists_measurable_schurCoordinateSpectrum n))
      (Ginibre.schurFlatEntryMeasurableEquiv n
        (fun ij => (x ij : ℂ))) = _
    rw [hflat]
    exact ((Classical.choose_spec
      (Ginibre.exists_measurable_schurCoordinateSpectrum n)).2 hmem).trans
        (Ginibre.schurCoordinateSpectrum_entrySplit _)
  have hpoly := Ginibre.charpoly_eq_prod_schurSpectrum A hsep
  change A.charpoly.roots = _
  rw [hlabels, hpoly, Polynomial.roots_prod]
  · simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton]
  · simpa only [← hpoly] using A.charpoly_monic.ne_zero

#print axioms realMatrixMeasurableRawSpectrum_roots_of_separable
end SpectralRadiusUpperTail

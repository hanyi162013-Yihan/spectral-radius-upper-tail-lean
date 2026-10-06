import SpectralRadiusUpperTail.RealGaussianMeasurableSpectrum

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Operator

/-- The lexicographic spectrum supplied by the audited complex Schur
library depends only on the characteristic polynomial on the simple
locus. In particular it cannot depend on strict-upper Schur entries. -/
theorem ginibreSchurSpectrum_eq_of_charpoly_eq
    {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.charpoly.Separable) (hB : B.charpoly.Separable)
    (hpoly : A.charpoly=B.charpoly) : Ginibre.schurSpectrum A=Ginibre.schurSpectrum B := by
  classical
  rw [Ginibre.schurSpectrum, dif_pos hA, Ginibre.schurSpectrum, dif_pos hB]
  let dA := Classical.choice (Ginibre.orderedSchurData_nonempty A hA)
  let dB := Classical.choice (Ginibre.orderedSchurData_nonempty B hB)
  change (fun i => dA.upper.val i i) = (fun i => dB.upper.val i i)
  apply Ginibre.ordered_upper_diagonals_eq_of_charpoly_eq dA.upper.val dB.upper.val
    dA.upper.property dB.upper.property dA.ordered dB.ordered
  calc
    dA.upper.val.charpoly = A.charpoly := by
      exact (Ginibre.charpoly_unitary_conjugate dA.frame.val dA.upper.val
        dA.frame.property).symm.trans (congrArg Matrix.charpoly dA.represents.symm)
    _ = B.charpoly := hpoly
    _ = dB.upper.val.charpoly := by
      exact (congrArg Matrix.charpoly dB.represents).trans
        (Ginibre.charpoly_unitary_conjugate dB.frame.val dB.upper.val dB.frame.property)

/-- The measurable real-matrix spectral representative agrees with the
canonical lexicographic spectrum at every simple matrix. -/
theorem realGaussianMeasurableRawSpectrum_eq_of_separable
    (n : ℕ) (a : (Fin n × Fin n) → ℝ)
    (ha : (Matrix.of a.curry).charpoly.Separable) :
    realGaussianMeasurableRawSpectrum n a =
      Ginibre.schurSpectrum ((Matrix.of a.curry).map Complex.ofRealHom) := by
  have hsep : ((Matrix.of a.curry).map Complex.ofRealHom).charpoly.Separable := by
    rw [Matrix.charpoly_map]
    exact (Polynomial.separable_map (algebraMap ℝ ℂ)).mpr ha
  have hmem := Ginibre.entrySplit_simple_mem_iUnion_schurDisjointEntryImage
    ((Matrix.of a.curry).map Complex.ofRealHom) hsep
  have hflat : Ginibre.schurFlatEntryMeasurableEquiv n
      (fun ij => (a ij : ℂ)) =
      Ginibre.schurEntrySplit n ((Matrix.of a.curry).map Complex.ofRealHom) := by
    rw [Ginibre.schurFlatEntryMeasurableEquiv_apply]
    congr 1
  change (Classical.choose (Ginibre.exists_measurable_schurCoordinateSpectrum n))
    (Ginibre.schurFlatEntryMeasurableEquiv n (fun ij => (a ij : ℂ))) = _
  rw [hflat]
  exact ((Classical.choose_spec
    (Ginibre.exists_measurable_schurCoordinateSpectrum n)).2 hmem).trans
      (Ginibre.schurCoordinateSpectrum_entrySplit _)

theorem realGaussianMeasurableRawSpectrum_eq_of_charpoly
    (n : ℕ) (a b : (Fin n × Fin n) → ℝ)
    (ha : (Matrix.of a.curry).charpoly.Separable)
    (hb : (Matrix.of b.curry).charpoly.Separable)
    (hab : (Matrix.of a.curry).charpoly=(Matrix.of b.curry).charpoly) :
    realGaussianMeasurableRawSpectrum n a = realGaussianMeasurableRawSpectrum n b := by
  rw [realGaussianMeasurableRawSpectrum_eq_of_separable n a ha,
    realGaussianMeasurableRawSpectrum_eq_of_separable n b hb]
  apply ginibreSchurSpectrum_eq_of_charpoly_eq
  · rw [Matrix.charpoly_map]
    exact (Polynomial.separable_map (algebraMap ℝ ℂ)).mpr ha
  · rw [Matrix.charpoly_map]
    exact (Polynomial.separable_map (algebraMap ℝ ℂ)).mpr hb
  · simp only [Matrix.charpoly_map, hab]

#print axioms ginibreSchurSpectrum_eq_of_charpoly_eq
#print axioms realGaussianMeasurableRawSpectrum_eq_of_separable
#print axioms realGaussianMeasurableRawSpectrum_eq_of_charpoly
end SpectralRadiusUpperTail

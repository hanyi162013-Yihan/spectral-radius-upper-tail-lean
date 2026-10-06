import SpectralRadiusUpperTail.RealGaussianCanonicalSpectrum
import SpectralRadiusUpperTail.RealMatrixMeasurableSpectrumRoots
import SpectralRadiusUpperTail.RealSchurMixedRegularDisjointAtlas

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Operator

noncomputable def realSchurMixedFlatEntries
    {m : ℕ} (s : Fin m → ℕ)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ) :
    (Fin (Fintype.card (RealSchurMixedCoord s)) ×
      Fin (Fintype.card (RealSchurMixedCoord s))) → ℝ :=
  fun ij => T ((Fintype.equivFin _).symm ij.1) ((Fintype.equivFin _).symm ij.2)

theorem realSchurMixedFlatEntries_charpoly
    {m : ℕ} (s : Fin m → ℕ)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ) :
    (Matrix.of (realSchurMixedFlatEntries s T).curry).charpoly=T.charpoly :=
  Matrix.charpoly_reindex (Fintype.equivFin _) T

/-- Canonical measurable eigenvalue labels in mixed block coordinates. -/
noncomputable def realSchurMixedCanonicalSpectrum
    {m : ℕ} (s : Fin m → ℕ)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ) :
    Fin (Fintype.card (RealSchurMixedCoord s)) → ℂ :=
  realGaussianMeasurableRawSpectrum _ (realSchurMixedFlatEntries s T)

theorem realSchurMixedCanonicalSpectrum_measurable
    {m : ℕ} (s : Fin m → ℕ) :
    Measurable (realSchurMixedCanonicalSpectrum s) := by
  apply (realGaussianMeasurableRawSpectrum_measurable _).comp
  exact (show Continuous (realSchurMixedFlatEntries s) by
    unfold realSchurMixedFlatEntries
    fun_prop).measurable

theorem realSchurMixedCanonicalSpectrum_eq_of_charpoly
    {m : ℕ} (s : Fin m → ℕ)
    (T U : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hT : T.charpoly.Separable) (hU : U.charpoly.Separable)
    (hpoly : T.charpoly=U.charpoly) :
    realSchurMixedCanonicalSpectrum s T=realSchurMixedCanonicalSpectrum s U := by
  apply realGaussianMeasurableRawSpectrum_eq_of_charpoly
  · rwa [realSchurMixedFlatEntries_charpoly]
  · rwa [realSchurMixedFlatEntries_charpoly]
  · simpa only [realSchurMixedFlatEntries_charpoly] using hpoly

theorem realSchurMixedCanonicalSpectrum_roots
    {m : ℕ} (s : Fin m → ℕ)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hT : T.charpoly.Separable) :
    (T.charpoly.map Complex.ofRealHom).roots =
      (Finset.univ : Finset (Fin (Fintype.card (RealSchurMixedCoord s)))).val.map
        (realSchurMixedCanonicalSpectrum s T) := by
  have hflat : (Matrix.of (realSchurMixedFlatEntries s T).curry).charpoly.Separable := by
    rwa [realSchurMixedFlatEntries_charpoly]
  have h := realMatrixMeasurableRawSpectrum_roots_of_separable _
    (realSchurMixedFlatEntries s T) hflat
  simpa only [Matrix.charpoly_map, realSchurMixedFlatEntries_charpoly,
    realSchurMixedCanonicalSpectrum] using h

theorem realSchurMixedCanonicalSpectrum_covers
    {m : ℕ} (s : Fin m → ℕ)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hT : T.charpoly.Separable)
    (z : ℂ) (hz : (T.charpoly.map Complex.ofRealHom).eval z=0) :
    ∃ i, realSchurMixedCanonicalSpectrum s T i=z := by
  have hmem : z ∈ (T.charpoly.map Complex.ofRealHom).roots :=
    (Polynomial.mem_roots (Polynomial.map_monic_ne_zero (Matrix.charpoly_monic T))).mpr hz
  rw [realSchurMixedCanonicalSpectrum_roots s T hT] at hmem
  obtain ⟨i,_,hi⟩ := Multiset.mem_map.mp hmem
  exact ⟨i,hi⟩

#print axioms realSchurMixedFlatEntries_charpoly
#print axioms realSchurMixedCanonicalSpectrum_measurable
#print axioms realSchurMixedCanonicalSpectrum_eq_of_charpoly
#print axioms realSchurMixedCanonicalSpectrum_roots
#print axioms realSchurMixedCanonicalSpectrum_covers
end SpectralRadiusUpperTail

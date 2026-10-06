import SpectralRadiusUpperTail.RealGaussianMeasurableSpectrum
import SpectralRadiusUpperTail.MatrixCharpolyScalarRoots
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory

/-- On the full-measure simple-spectrum locus, the measurable ordering from
the complex Schur atlas reproduces the actual complex roots of the real
Gaussian characteristic polynomial, including multiplicity. -/
theorem realGaussianMeasurableRawSpectrum_roots_ae (n : ℕ) :
    ∀ᵐ x ∂gaussianMatrixLaw n,
      ((Matrix.of x.curry).map Complex.ofRealHom).charpoly.roots =
        (Finset.univ : Finset (Fin n)).val.map
          (realGaussianMeasurableRawSpectrum n x) := by
  classical
  filter_upwards [realGaussianMatrix_charpoly_separable_ae n,
    realGaussianMeasurableRawSpectrum_eq_ae n] with x hx hxg
  let A : Matrix (Fin n) (Fin n) ℂ :=
    (Matrix.of x.curry).map Complex.ofRealHom
  have hsep : A.charpoly.Separable := by
    dsimp [A]
    rw [Matrix.charpoly_map]
    exact (Polynomial.separable_map (algebraMap ℝ ℂ)).mpr hx
  have hpoly := Ginibre.charpoly_eq_prod_schurSpectrum A hsep
  rw [hxg]
  change A.charpoly.roots = _
  rw [hpoly, Polynomial.roots_prod]
  · simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton]
    rfl
  · simpa only [← hpoly] using A.charpoly_monic.ne_zero

/-- The same measurable labels describe the roots after the `n⁻¹ᐟ²`
normalization used in the spectral-radius problem. -/
theorem realGaussianMeasurableNormalizedSpectrum_roots_ae
    (n : ℕ) (hn : 0 < n) :
    ∀ᵐ x ∂gaussianMatrixLaw n,
      (((1/Real.sqrt (n : ℝ)) • Matrix.of x.curry).map
        Complex.ofRealHom).charpoly.roots =
        (Finset.univ : Finset (Fin n)).val.map
          (fun i => (((1/Real.sqrt (n : ℝ)) : ℝ) : ℂ) *
            realGaussianMeasurableRawSpectrum n x i) := by
  classical
  let c : ℂ := (((1/Real.sqrt (n : ℝ)) : ℝ) : ℂ)
  have hsqrt : 0 < Real.sqrt (n : ℝ) :=
    Real.sqrt_pos.2 (Nat.cast_pos.mpr hn)
  have hc : c ≠ 0 := by
    dsimp [c]
    exact Complex.ofReal_ne_zero.mpr (one_div_ne_zero hsqrt.ne')
  filter_upwards [realGaussianMeasurableRawSpectrum_roots_ae n] with x hx
  let A : Matrix (Fin n) (Fin n) ℂ :=
    (Matrix.of x.curry).map Complex.ofRealHom
  have hmatrix : (((1/Real.sqrt (n : ℝ)) • Matrix.of x.curry).map
      Complex.ofRealHom) = c • A := by
    ext i j
    simp [A, c, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  rw [hmatrix, matrix_charpoly_smul_roots A c hc]
  change A.charpoly.roots.map (fun z => c*z) = _
  rw [hx]
  simp only [Multiset.map_map]
  rfl

#print axioms realGaussianMeasurableRawSpectrum_roots_ae
#print axioms realGaussianMeasurableNormalizedSpectrum_roots_ae
end SpectralRadiusUpperTail

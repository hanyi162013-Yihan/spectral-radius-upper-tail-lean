import SpectralRadiusUpperTail.MarkedRealEigenlineBasis
import SpectralRadiusUpperTail.RealSchurMixedUpperAlgebra
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- An eigenvector in the first slot kills every entry in the lower-left
block of its orthonormal-basis matrix. -/
theorem markedRealEigenlineBasis_lowerLeft_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (m : ℕ)
    (f : E →ₗ[ℝ] E) (b : OrthonormalBasis
      (RealSchurMixedCoord (markedRealTwoBlockSizes m)) ℝ E)
    (x : ℝ)
    (hf : f (b (markedRealFirstCoordinate m)) =
      x • b (markedRealFirstCoordinate m))
    (i : Fin m) :
    (LinearMap.toMatrix b.toBasis b.toBasis f)
      ⟨1,i⟩ (markedRealFirstCoordinate m) = 0 := by
  rw [LinearMap.toMatrix_apply, b.coe_toBasis_repr_apply]
  change b.repr (f (b (markedRealFirstCoordinate m))) ⟨1,i⟩ = 0
  rw [hf, map_smul]
  simp [OrthonormalBasis.repr_self, markedRealFirstCoordinate]

/-- Every unit real eigenvector of a simple-spectrum matrix yields an
adapted regular two-block center. The existence of this center is one
piece of global marked-line chart coverage. -/
theorem exists_markedRealEigenline_blockUpper
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (m : ℕ)
    (hdim : Module.finrank ℝ E = m+1)
    (f : E →ₗ[ℝ] E) (v : E) (hv : ‖v‖ = 1)
    (x : ℝ) (hfv : f v = x • v) :
    ∃ b : OrthonormalBasis (RealSchurMixedCoord (markedRealTwoBlockSizes m)) ℝ E,
      b (markedRealFirstCoordinate m) = v ∧
      realSchurMixedLowerProjection (markedRealTwoBlockSizes m)
        (LinearMap.toMatrix b.toBasis b.toBasis f) = 0 := by
  obtain ⟨b,hb⟩ := exists_markedRealEigenlineBasis m hdim v hv
  refine ⟨b,hb,?_⟩
  apply (realSchurMixed_blockTriangular_iff_lower_zero _ _).mp
  rintro ⟨a,i⟩ ⟨c,j⟩ hca
  change c < a at hca
  have ha : a = (1 : Fin 2) := by apply Fin.ext; omega
  have hc : c = (0 : Fin 2) := by apply Fin.ext; omega
  subst a
  subst c
  have hj : j = markedRealZeroCoordinate m := by
    apply Fin.ext
    simp [markedRealTwoBlockSizes, markedRealZeroCoordinate] at j ⊢
  subst j
  exact markedRealEigenlineBasis_lowerLeft_zero m f b x
    (by simpa only [hb] using hfv) i

#print axioms markedRealEigenlineBasis_lowerLeft_zero
#print axioms exists_markedRealEigenline_blockUpper
end SpectralRadiusUpperTail

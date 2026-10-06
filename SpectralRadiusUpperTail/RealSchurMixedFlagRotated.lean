import SpectralRadiusUpperTail.RealSchurMixedFlagLocal

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Operator

noncomputable def realSchurMixedMarkerRotatedChart
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (c : Fin m → ℝ) (hc : Function.Injective c)
    (R : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hR : Rᵀ*R=1) :
    OpenPartialHomeomorph (RealSchurMixedTangent s)
      (Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ) :=
  (realSchurMixedMarkerChart s hs c hc).transHomeomorph
    (realMatrixOrthogonalConjugationEquiv _ R hR).toContinuousLinearEquiv.toHomeomorph

theorem realSchurMixedMarkerRotatedChart_apply
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (c : Fin m → ℝ) (hc : Function.Injective c)
    (R : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hR : Rᵀ*R=1) (x : RealSchurMixedTangent s) :
    realSchurMixedMarkerRotatedChart s hs c hc R hR x =
      R*(realSchurMixedMarkerChart s hs c hc x)*Rᵀ := rfl

theorem realSchurMixedMarkerRotatedChart_center_mem_target
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (c : Fin m → ℝ) (hc : Function.Injective c)
    (R : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hR : Rᵀ*R=1) :
    R*realSchurMixedBlockScalar s c*Rᵀ ∈
      (realSchurMixedMarkerRotatedChart s hs c hc R hR).target := by
  have h0 : 0 ∈ (realSchurMixedMarkerRotatedChart s hs c hc R hR).source :=
    realSchurMixedMarkerChart_zero_mem_source s hs c hc
  have h := (realSchurMixedMarkerRotatedChart s hs c hc R hR).map_source h0
  rwa [realSchurMixedMarkerRotatedChart_apply, realSchurMixedMarkerChart_apply,
    realSchurMixedExpCoordinates_zero] at h

/-- Rotated marker charts cover their local marker orbit using only the
angle variable. All actual Schur matrix entries can subsequently vary. -/
theorem realSchurMixedFlagMarker_rotated_coverage
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (c : Fin m → ℝ) (hc : Function.Injective c)
    (R : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hR : Rᵀ*R=1)
    (A : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hA : A ∈ (realSchurMixedMarkerRotatedChart s hs c hc R hR).target)
    (hHerm : A.IsHermitian)
    (hpoly : A.charpoly = (realSchurMixedBlockScalar s c).charpoly) :
    ∃ w ∈ realSchurMixedFlagDomain s hs c hc,
      R*(realSchurMixedFlagMarker s c w)*Rᵀ = A := by
  let C := realSchurMixedMarkerRotatedChart s hs c hc R hR
  let x := C.symm A
  have hx : x ∈ (realSchurMixedMarkerChart s hs c hc).source := C.map_target hA
  have hmap : C x = A := C.right_inv hA
  have hrecover : realSchurMixedMarkerChart s hs c hc x = Rᵀ*A*R := by
    rw [← hmap]
    change _ = Rᵀ*(R*(realSchurMixedMarkerChart s hs c hc x)*Rᵀ)*R
    simp only [Matrix.mul_assoc, hR, Matrix.mul_one]
    rw [← Matrix.mul_assoc, hR, Matrix.one_mul]
  have hHermC : (realSchurMixedMarkerChart s hs c hc x).IsHermitian := by
    rw [hrecover]
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.isHermitian_conjTranspose_mul_mul R hHerm
  have hpolyC : (realSchurMixedMarkerChart s hs c hc x).charpoly =
      (realSchurMixedBlockScalar s c).charpoly := by
    rw [← hmap] at hpoly
    change (R*(realSchurMixedMarkerChart s hs c hc x)*Rᵀ).charpoly = _ at hpoly
    rwa [realMatrixOrthogonalConjugation_charpoly _ R _ hR] at hpoly
  have hz := realSchurMixedMarkerChart_upper_zero s hs c hc x hx hHermC hpolyC
  have hpair : (x.1,(0 : realSchurMixedUpperSubmodule s)) = x := Prod.ext rfl hz.symm
  refine ⟨x.1,?_,?_⟩
  · change (x.1,(0 : realSchurMixedUpperSubmodule s)) ∈
      (realSchurMixedMarkerChart s hs c hc).source
    rwa [hpair]
  · rw [realSchurMixedFlagMarker_eq_chart s hs c hc, hpair]
    exact hmap

#print axioms realSchurMixedMarkerRotatedChart_apply
#print axioms realSchurMixedMarkerRotatedChart_center_mem_target
#print axioms realSchurMixedFlagMarker_rotated_coverage
end SpectralRadiusUpperTail

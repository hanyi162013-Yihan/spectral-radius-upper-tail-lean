import SpectralRadiusUpperTail.RealSchurMixedAngularJacobian
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Operator

/-- The genuine Fréchet derivative expressed in the moving orthogonal
output frame and fixed lower/upper entry coordinates. -/
noncomputable def realSchurMixedRotatedDifferential
    {m : ℕ} (s : Fin m → ℕ)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (x : RealSchurMixedTangent s) :
    RealSchurMixedTangent s →ₗ[ℝ] RealSchurMixedTangent s :=
  (realSchurMixedEntryEquiv s).toLinearMap.comp ({
    toFun v := (realSchurMixedAngularFrame s x.1)ᵀ *
      fderiv ℝ (realSchurMixedExpCoordinates s T) x v *
        realSchurMixedAngularFrame s x.1
    map_add' v u := by rw [map_add, Matrix.mul_add, Matrix.add_mul]
    map_smul' a v := by rw [map_smul, Matrix.mul_smul, Matrix.smul_mul]; rfl } :
      RealSchurMixedTangent s →ₗ[ℝ]
        Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)

theorem realSchurMixedRotatedDifferential_eq
    {m : ℕ} (s : Fin m → ℕ)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (x : RealSchurMixedTangent s) :
    realSchurMixedRotatedDifferential s T x =
      (realSchurMixedEntryEquiv s).toLinearMap.comp
        (realSchurMixedMovingTangentMap s (T+x.2.val)
          (realSchurMixedMaurerCartan s x.1)) := by
  apply LinearMap.ext
  intro v
  exact congrArg (realSchurMixedEntryEquiv s)
    (realSchurMixedExpCoordinates_fderiv_rotated s T x v)

/-- The moving-frame Jacobian at every angular and block-upper parameter.
The two factors separate exactly. -/
theorem realSchurMixedRotatedDifferential_det
    {m : ℕ} (s : Fin m → ℕ)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hT : realSchurMixedLowerProjection s T = 0)
    (x : RealSchurMixedTangent s) :
    LinearMap.det (realSchurMixedRotatedDifferential s T x) =
      (realSchurMixedOrbitMatrix s (T+x.2.val)).det *
        realSchurMixedAngularJacobian s x.1 := by
  rw [realSchurMixedRotatedDifferential_eq]
  apply realSchurMixedMovingTangentMap_det
  have hx : realSchurMixedLowerProjection s x.2.val = 0 := x.2.property
  rw [map_add, hT, hx, add_zero]

/-- The block-upper factor itself splits into the local Sylvester
determinants at every parameter. -/
theorem realSchurMixedRotatedDifferential_det_sylvester
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hT : realSchurMixedLowerProjection s T = 0)
    (x : RealSchurMixedTangent s) :
    LinearMap.det (realSchurMixedRotatedDifferential s T x) =
      (∏ p : RealSchurLowerIndex m,
        (realSchurMixedSylvester s (T+x.2.val) p).det) *
        realSchurMixedAngularJacobian s x.1 := by
  rw [realSchurMixedRotatedDifferential_det s T hT x]
  congr 1
  apply realSchurMixedOrbitMatrix_det s hs
  intro a b hba u v
  have hupper : realSchurMixedLowerProjection s (T+x.2.val) = 0 := by
    have hx : realSchurMixedLowerProjection s x.2.val = 0 := x.2.property
    rw [map_add, hT, hx, add_zero]
  exact (realSchurMixed_blockTriangular_iff_lower_zero s _).mpr hupper
    (i := ⟨a,u⟩) (j := ⟨b,v⟩) hba

#print axioms realSchurMixedRotatedDifferential_det
#print axioms realSchurMixedRotatedDifferential_det_sylvester
end SpectralRadiusUpperTail

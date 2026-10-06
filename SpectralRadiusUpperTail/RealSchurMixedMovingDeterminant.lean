import SpectralRadiusUpperTail.RealSchurMixedMovingFrame
import Ginibre.BlockLinearDeterminant
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- The full tangent with an arbitrary real-linear angular frame. -/
def realSchurMixedMovingTangentMap
    {m : ℕ} (s : Fin m → ℕ)
    (S : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (K : (RealSchurMixedOrbitIndex s → ℝ) →ₗ[ℝ]
      Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ) :
    RealSchurMixedTangent s →ₗ[ℝ]
      Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ where
  toFun x := x.2.val + (K x.1*S-S*K x.1)
  map_add' x y := by
    change (x.2.val+y.2.val) +
      (K (x.1+y.1)*S-S*K (x.1+y.1)) = _
    rw [map_add, Matrix.add_mul, Matrix.mul_add]
    abel
  map_smul' a x := by
    change (a • x.2.val) + (K (a • x.1)*S-S*K (a • x.1)) = _
    rw [map_smul, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_sub]
    rfl

theorem realSchurMixedMovingTangentMap_upper
    {m : ℕ} (s : Fin m → ℕ)
    (S : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (K : (RealSchurMixedOrbitIndex s → ℝ) →ₗ[ℝ]
      Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (D : realSchurMixedUpperSubmodule s) :
    realSchurMixedMovingTangentMap s S K (0,D) = D.val := by
  change D.val + (K 0*S-S*K 0) = D.val
  rw [map_zero, Matrix.zero_mul, Matrix.mul_zero, sub_self, add_zero]

/-- The complete moving-frame determinant factors into the spectral
matrix determinant and an angular determinant, with no restriction on
the angular linear map. -/
theorem realSchurMixedMovingTangentMap_det
    {m : ℕ} (s : Fin m → ℕ)
    (S : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hS : realSchurMixedLowerProjection s S = 0)
    (K : (RealSchurMixedOrbitIndex s → ℝ) →ₗ[ℝ]
      Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ) :
    LinearMap.det ((realSchurMixedEntryEquiv s).toLinearMap.comp
      (realSchurMixedMovingTangentMap s S K)) =
      (realSchurMixedOrbitMatrix s S).det *
        LinearMap.det ((-(realSchurMixedLowerProjection s).toLinearMap).comp K) := by
  have hd : LinearMap.det ((realSchurMixedEntryEquiv s).toLinearMap.comp
      (realSchurMixedMovingTangentMap s S K)) =
      LinearMap.det ((Matrix.toLin' (realSchurMixedOrbitMatrix s S)).comp
        ((-(realSchurMixedLowerProjection s).toLinearMap).comp K)) := by
    apply Ginibre.det_block_lower_identity
    · intro x
      change realSchurMixedLowerProjection s
        (x.2.val + (K x.1*S-S*K x.1)) = _
      rw [map_add, show realSchurMixedLowerProjection s x.2.val = 0 from x.2.property,
        zero_add, realSchurMixedLowerProjection_commutator s S (K x.1) hS]
      change -(realSchurMixedOrbitMatrix s S *ᵥ
        realSchurMixedLowerProjection s (K x.1)) =
        realSchurMixedOrbitMatrix s S *ᵥ
          (-realSchurMixedLowerProjection s (K x.1))
      rw [Matrix.mulVec_neg]
    · intro D
      change realSchurMixedUpperEntries s
        (realSchurMixedMovingTangentMap s S K (0,D)) = D
      rw [realSchurMixedMovingTangentMap_upper,
        realSchurMixedUpperEntries_upper]
  rw [hd, LinearMap.det_comp, LinearMap.det_toLin']

#print axioms realSchurMixedMovingTangentMap_det
end SpectralRadiusUpperTail

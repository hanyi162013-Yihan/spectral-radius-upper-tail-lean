import SpectralRadiusUpperTail.MarkedRealAngularFirstColumn
import SpectralRadiusUpperTail.MarkedRealRotatedColumnUniqueness
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- A product angular Schur chart is injective at a fixed simple marked
root: once the first-column sign is chosen, neither the angular variable
nor any block-upper matrix coordinate can collide. Its angular domain is
independent of the scalar root and complementary matrix. -/
theorem markedRealAngular_upperProduct_injective_at_root
    (m : ℕ)
    (w v : RealSchurMixedOrbitIndex (markedRealTwoBlockSizes m) → ℝ)
    (S T : Matrix (RealSchurMixedCoord (markedRealTwoBlockSizes m))
      (RealSchurMixedCoord (markedRealTwoBlockSizes m)) ℝ)
    (hw : w ∈ (realSchurMixedAngularProjectionChart
      (markedRealTwoBlockSizes m)).source)
    (hv : v ∈ (realSchurMixedAngularProjectionChart
      (markedRealTwoBlockSizes m)).source)
    (hwpos : 0 < (realSchurMixedAngularFrame
      (markedRealTwoBlockSizes m) w)
        (markedRealFirstCoordinate m) (markedRealFirstCoordinate m))
    (hvpos : 0 < (realSchurMixedAngularFrame
      (markedRealTwoBlockSizes m) v)
        (markedRealFirstCoordinate m) (markedRealFirstCoordinate m))
    (hS : realSchurMixedLowerProjection (markedRealTwoBlockSizes m) S = 0)
    (hT : realSchurMixedLowerProjection (markedRealTwoBlockSizes m) T = 0)
    (hscalar : markedRealScalar m S = markedRealScalar m T)
    (hA : (realSchurMixedAngularFrame (markedRealTwoBlockSizes m) w) * S *
        (realSchurMixedAngularFrame (markedRealTwoBlockSizes m) w)ᵀ =
      (realSchurMixedAngularFrame (markedRealTwoBlockSizes m) v) * T *
        (realSchurMixedAngularFrame (markedRealTwoBlockSizes m) v)ᵀ)
    (hsep : ((realSchurMixedAngularFrame
      (markedRealTwoBlockSizes m) w) * S *
        (realSchurMixedAngularFrame (markedRealTwoBlockSizes m) w)ᵀ).charpoly.Separable) :
    w = v ∧ S = T := by
  let Q := realSchurMixedAngularFrame (markedRealTwoBlockSizes m) w
  let R := realSchurMixedAngularFrame (markedRealTwoBlockSizes m) v
  have hQ : Qᵀ*Q=1 := realSchurMixedAngularFrame_orthogonal _ w
  have hR : Rᵀ*R=1 := realSchurMixedAngularFrame_orthogonal _ v
  have hcol : ∀ i, Q i (markedRealFirstCoordinate m) =
      R i (markedRealFirstCoordinate m) :=
    markedRealUpper_rotatedColumns_eq_of_sameRoot m
      (Q*S*Qᵀ) Q R S T hsep hS hT hQ hR rfl hA
      hscalar hwpos hvpos
  have hwv : w = v := by
    apply markedRealAngularFrame_firstColumn_injOn m w v hw hv
    intro i
    exact hcol ⟨1,i⟩
  refine ⟨hwv, ?_⟩
  subst v
  have hST : Q*S*Qᵀ = Q*T*Qᵀ := hA
  have hQT : Qᵀ*(Q*S*Qᵀ)*Q = Qᵀ*(Q*T*Qᵀ)*Q :=
    congrArg (fun X => Qᵀ*X*Q) hST
  simpa only [Matrix.mul_assoc, ← Matrix.mul_assoc Qᵀ Q,
    hQ, Matrix.one_mul, Matrix.mul_one] using hQT

#print axioms markedRealAngular_upperProduct_injective_at_root
end SpectralRadiusUpperTail

import SpectralRadiusUpperTail.RealSchurMixedOrbitSupport
import SpectralRadiusUpperTail.SigmaBlockTriangularDeterminant
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- The full lower-block angular Jacobian for a real Schur pattern of
arbitrary positive block sizes is the product of local Sylvester
determinants. In the real Gaussian application the sizes are one or two. -/
theorem realSchurMixedOrbitMatrix_det
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hT : ∀ a b : Fin m, b < a → ∀ x : Fin (s a),
      ∀ y : Fin (s b), T ⟨a,x⟩ ⟨b,y⟩ = 0) :
    (realSchurMixedOrbitMatrix s T).det =
      ∏ p : RealSchurLowerIndex m,
        (realSchurMixedSylvester s T p).det := by
  classical
  have hbridge (p : RealSchurLowerIndex m) :
      Nonempty (RealSchurMixedBridge s p) :=
    ⟨⟨⟨0,hs p.1.1⟩,⟨0,hs p.1.2⟩⟩⟩
  have htri := realSchurMixedOrbitMatrix_blockTriangular s T hT
  calc
    (realSchurMixedOrbitMatrix s T).det =
        ∏ p : RealSchurLowerIndex m,
          (Matrix.of (fun r z : RealSchurMixedBridge s p =>
            realSchurMixedOrbitMatrix s T ⟨p,r⟩ ⟨p,z⟩)).det :=
      determinant_of_sigma_block_triangular
        (RealSchurMixedBridge s) hbridge realSchurLowerKey
        realSchurLowerKey_injective (realSchurMixedOrbitMatrix s T) htri
    _ = _ := by
      apply Finset.prod_congr rfl
      intro p _
      congr 1
      ext r z
      exact realSchurMixedOrbitMatrix_diagonal s T p r z

#print axioms realSchurMixedOrbitMatrix_det
end SpectralRadiusUpperTail

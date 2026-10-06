import SpectralRadiusUpperTail.RealSchurPaddedRadius
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix.Norms.L2Operator

/-- The radius determined by a mixed list of real Schur diagonal blocks.
The zero-bridge reference matrix is only a way to define the maximum
without imposing a nonempty-block condition. -/
noncomputable def realSchurDataIntrinsicRadius {N : ℕ}
    (B : Fin N → RealSchurBlockData) : ℝ :=
  (spectralRadius ℂ ((flattenSchurBlocks
    (realSchurPaddedMatrix 1 B 0)).map Complex.ofRealHom)).toReal

theorem realSchurDataIntrinsicRadius_nonneg {N : ℕ}
    (B : Fin N → RealSchurBlockData) :
    0 ≤ realSchurDataIntrinsicRadius B := by
  unfold realSchurDataIntrinsicRadius
  exact ENNReal.toReal_nonneg

theorem realSchurDataRadius_le_intrinsic {N : ℕ}
    (B : Fin N → RealSchurBlockData) (i : Fin N) :
    realSchurDataRadius (B i) ≤ realSchurDataIntrinsicRadius B := by
  exact realSchurDataRadius_le_paddedMatrix_radius 1 B 0 i

/-- The flattened product-model radius depends only on diagonal block data;
it is independent of the gap and Gaussian bridge coordinates and of the
bridge normalization parameter. -/
theorem realSchurPaddedMatrix_radius_eq_intrinsic {N : ℕ}
    (n : ℕ) (B : Fin N → RealSchurBlockData)
    (z : (Fin N → ℝ) × (SchurEntryIndex N 2 → ℝ)) :
    (spectralRadius ℂ ((flattenSchurBlocks
      (realSchurPaddedMatrix n B z)).map Complex.ofRealHom)).toReal =
      realSchurDataIntrinsicRadius B := by
  have hupper :
      (spectralRadius ℂ ((flattenSchurBlocks
        (realSchurPaddedMatrix n B z)).map Complex.ofRealHom)).toReal ≤
        realSchurDataIntrinsicRadius B :=
    realSchurPaddedMatrix_radius_le n B z _
      (realSchurDataIntrinsicRadius_nonneg B)
      (realSchurDataRadius_le_intrinsic B)
  have hnonneg :
      0 ≤ (spectralRadius ℂ ((flattenSchurBlocks
        (realSchurPaddedMatrix n B z)).map Complex.ofRealHom)).toReal :=
    ENNReal.toReal_nonneg
  have hlower : realSchurDataIntrinsicRadius B ≤
      (spectralRadius ℂ ((flattenSchurBlocks
        (realSchurPaddedMatrix n B z)).map Complex.ofRealHom)).toReal := by
    unfold realSchurDataIntrinsicRadius
    exact realSchurPaddedMatrix_radius_le 1 B 0 _ hnonneg
      (realSchurDataRadius_le_paddedMatrix_radius n B z)
  exact le_antisymm hupper hlower

#print axioms realSchurDataIntrinsicRadius_nonneg
#print axioms realSchurDataRadius_le_intrinsic
#print axioms realSchurPaddedMatrix_radius_eq_intrinsic
end SpectralRadiusUpperTail

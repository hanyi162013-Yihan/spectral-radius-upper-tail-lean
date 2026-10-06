import SpectralRadiusUpperTail.RealSchurNativeMatrixTransfer
import SpectralRadiusUpperTail.RealSchurNativeProbabilityTransport
import SpectralRadiusUpperTail.FiniteRealMatrixObservables
import SpectralRadiusUpperTail.RealSchurDataIntrinsicRadius

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Frobenius

theorem realSchurNative_scaled_matrix_identity {m : ℕ}
    (s : Fin m → ℕ) (hs : ∀ i, s i=1 ∨ s i=2) (hsmall : ∀ i, s i ≤ 2)
    (n : ℕ) (hn : 0 < n) (x u : Fin m → ℝ) (hu : ∀ i, s i=2 → 0 ≤ u i)
    (z : (Fin m → ℝ) × (SchurEntryIndex m 2 → ℝ)) (hg : ∀ i, s i=2 → 0 ≤ z.1 i) :
    (flattenSchurBlocks (realSchurPaddedMatrix n
      (fun i => realSchurNativeBlockData (s i) (x i/Real.sqrt n) (u i/(n : ℝ)))
        (realSchurNativeCommonScale n z))).submatrix
          (realSchurNativeCoordEmbedding s hsmall) (realSchurNativeCoordEmbedding s hsmall)=
      (1/Real.sqrt n) • realSchurMixedUpperEntryJoin s
        (realSchurCanonicalDiagonal s x u z.1) (realSchurNativeUpperSelect s hsmall z.2) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [realSchurNativePadded_restrict s hs hsmall n _ _
    (fun i hi => div_nonneg (hu i hi) hnR.le) _
    (fun i hi => div_nonneg (hg i hi) hnR.le)]
  exact realSchurCanonicalJoin_scale s x u z.1 _ (n : ℝ) hnR

theorem realSchurNative_scaled_radius_identity {m : ℕ}
    (s : Fin m → ℕ) (hs : ∀ i, s i=1 ∨ s i=2) (hsmall : ∀ i, s i ≤ 2)
    (n : ℕ) (hn : 0 < n) (x u : Fin m → ℝ) (hu : ∀ i, s i=2 → 0 ≤ u i)
    (z : (Fin m → ℝ) × (SchurEntryIndex m 2 → ℝ)) (hg : ∀ i, s i=2 → 0 ≤ z.1 i) :
    finiteRealMatrixRadius ((1/Real.sqrt n) • realSchurMixedUpperEntryJoin s
      (realSchurCanonicalDiagonal s x u z.1) (realSchurNativeUpperSelect s hsmall z.2))=
      realSchurDataIntrinsicRadius
        (fun i => realSchurNativeBlockData (s i) (x i/Real.sqrt n) (u i/(n : ℝ))) := by
  let B := fun i => realSchurNativeBlockData (s i) (x i/Real.sqrt n) (u i/(n : ℝ))
  let z' := realSchurNativeCommonScale n z
  let M := flattenSchurBlocks (realSchurPaddedMatrix n B z')
  have hl : ∀ a b, a ∉ Set.range (realSchurNativeCoordEmbedding s hsmall) → M a b=0 := by
    intro a b ha
    rw [realSchurNativeCoordEmbedding_range] at ha
    exact realSchurNativePadded_inactive_left s hs n _ _ z' a b (Nat.le_of_not_lt ha)
  have hr : ∀ a b, b ∉ Set.range (realSchurNativeCoordEmbedding s hsmall) → M a b=0 := by
    intro a b hb
    rw [realSchurNativeCoordEmbedding_range] at hb
    exact realSchurNativePadded_inactive_right s hs n _ _ z' a b (Nat.le_of_not_lt hb)
  have he := congrArg ENNReal.toReal
    (finiteCoordinateMatrix_radius (realSchurNativeCoordEmbedding s hsmall) M hl hr)
  change finiteRealMatrixRadius M=finiteRealMatrixRadius
    (M.submatrix (realSchurNativeCoordEmbedding s hsmall) (realSchurNativeCoordEmbedding s hsmall)) at he
  dsimp only [M,B,z'] at he
  rw [realSchurNative_scaled_matrix_identity s hs hsmall n hn x u hu z hg] at he
  exact he.symm.trans (realSchurPaddedMatrix_radius_eq_intrinsic n B z')

#print axioms realSchurNative_scaled_matrix_identity
#print axioms realSchurNative_scaled_radius_identity
end SpectralRadiusUpperTail

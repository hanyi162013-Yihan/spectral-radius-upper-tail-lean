import SpectralRadiusUpperTail.RealSchurNativeBlockSpectralRotation
import SpectralRadiusUpperTail.RealSchurAtomicDiagonalWeightInvariance
import SpectralRadiusUpperTail.RealSchurGaussianUpperObservable

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped Matrix Matrix.Norms.Operator ENNReal

noncomputable def realSchurAtomicCoreWeight
    {n : ℕ} (F : RealSchurFiniteAtlas n) (I : RealSchurFiniteCode n) (k : ℕ)
    (H : Matrix (RealSchurMixedCoord I.1.sizes) (RealSchurMixedCoord I.1.sizes) ℝ → ℝ≥0∞) :
    (RealSchurMixedDiagonalEntry I.1.sizes → ℝ) → ℝ≥0∞ :=
  (realSchurAtomicDiagonalSource I.1.sizes I.2.2).indicator
    (fun d => (ENNReal.ofReal (realSchurMixedDiagonalGapWeight I.1.sizes d) *
      realSchurAtomicDiagonalMultiplicityWeight F I k d) * realSchurGaussianUpperIntegral I.1.sizes H d)

theorem realSchurMixedDiagonalGapWeight_continuous
    {m : ℕ} (s : Fin m → ℕ) : Continuous (realSchurMixedDiagonalGapWeight s) := by
  unfold realSchurMixedDiagonalGapWeight
  apply continuous_finsetProd
  intro p _
  apply Continuous.abs
  apply Continuous.matrix_det
  apply continuous_matrix
  intro i j
  unfold realSchurMixedSylvester realSchurMixedUpperEntryJoin
  split_ifs <;> fun_prop

theorem realSchurAtomicCoreWeight_measurable
    {n : ℕ} (F : RealSchurFiniteAtlas n) (I : RealSchurFiniteCode n) (k : ℕ)
    (H : Matrix (RealSchurMixedCoord I.1.sizes) (RealSchurMixedCoord I.1.sizes) ℝ → ℝ≥0∞)
    (hH : Measurable H) : Measurable (realSchurAtomicCoreWeight F I k H) :=
  (((realSchurMixedDiagonalGapWeight_continuous I.1.sizes).measurable.ennreal_ofReal.mul
    (realSchurAtomicDiagonalMultiplicityWeight_measurable F I k)).mul
      (realSchurGaussianUpperIntegral_measurable I.1.sizes H hH)).indicator
        (measurableSet_realSchurAtomicDiagonalSource I.1.sizes I.2.2)

/-- Once the independent diagonal Gaussian densities are removed, every
remaining factor of the actual atlas integral is blockwise orthogonally
invariant for a conjugation-invariant matrix observable. -/
theorem realSchurAtomicCoreWeight_block_rotation
    {n : ℕ} (F : RealSchurFiniteAtlas n) (I : RealSchurFiniteCode n) (k : ℕ)
    (H : Matrix (RealSchurMixedCoord I.1.sizes) (RealSchurMixedCoord I.1.sizes) ℝ → ℝ≥0∞)
    (hH : Measurable H)
    (hInv : ∀ W : Matrix (RealSchurMixedCoord I.1.sizes) (RealSchurMixedCoord I.1.sizes) ℝ,
      Wᵀ*W=1 → ∀ A, H (W*A*Wᵀ)=H A)
    (Q : (i : Fin I.1.blockCount) → Matrix (Fin (I.1.sizes i)) (Fin (I.1.sizes i)) ℝ)
    (hQ : ∀ i, (Q i)ᵀ*Q i=1) (d : RealSchurMixedDiagonalEntry I.1.sizes → ℝ) :
    realSchurAtomicCoreWeight F I k H
      (realSchurMixedDiagonalConjugation I.1.sizes (Matrix.blockDiagonal' Q) d)=
        realSchurAtomicCoreWeight F I k H d := by
  classical
  let W := Matrix.blockDiagonal' Q
  have hW : Wᵀ*W=1 := realSchurMixed_blockDiagonal_orthogonal I.1.sizes Q hQ
  have hoff := realSchurMixed_blockDiagonal_off I.1.sizes Q
  unfold realSchurAtomicCoreWeight
  simp only [Set.indicator_apply,
    realSchurAtomicDiagonalSource_block_rotation I.1.sizes I.1.sizes_pos I.2.2 Q hQ d,
    realSchurMixedDiagonalGapWeight_block_rotation I.1.sizes I.1.sizes_small Q hQ d,
    realSchurAtomicDiagonalMultiplicityWeight_conjugation F I k (Matrix.blockDiagonal' Q) hW hoff d,
    realSchurGaussianUpperIntegral_conjugation I.1.sizes (Matrix.blockDiagonal' Q) hW hoff H hH
      (hInv (Matrix.blockDiagonal' Q) hW) d]

#print axioms realSchurMixedDiagonalGapWeight_continuous
#print axioms realSchurAtomicCoreWeight_measurable
#print axioms realSchurAtomicCoreWeight_block_rotation
end SpectralRadiusUpperTail

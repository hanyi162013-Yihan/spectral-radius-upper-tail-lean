import SpectralRadiusUpperTail.GaussianStoppedTruncationError
import SpectralRadiusUpperTail.GaussianMatrixTerminalSum
import SpectralRadiusUpperTail.GaussianMatrixStopping

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators Matrix.Norms.Frobenius
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂] {N : ℕ}

/-- The actual matrix difference, on the same fixed coupled array. -/
noncomputable def gaussianMatrixTruncationError (μ : Measure 𝕂) [SFinite μ]
    (v : ℕ → 𝕂) (a : ℝ) (t : Fin N → 𝕂) (K R : ℝ)
    (x : Fin N → Fin N → 𝕂 × 𝕂) : Matrix (Fin N) (Fin N) 𝕂 :=
  gaussianStoppedMatrix μ v a t K x-gaussianTruncatedMatrix μ v a t K R x

lemma gaussianMatrixTruncationError_apply (μ : Measure 𝕂) [SFinite μ]
    (v : ℕ → 𝕂) (a : ℝ) (t : Fin N → 𝕂) (K R : ℝ)
    (x : Fin N → Fin N → 𝕂 × 𝕂) (i j : Fin N) :
    gaussianMatrixTruncationError μ v a t K R x i j =
      (1/Real.sqrt (N : ℝ) : ℝ) • gaussianStoppedTruncationError μ v a N (t i) K R (N-(j.val+1)) (x i) := by
  change (1/Real.sqrt (N : ℝ) : ℝ) • gaussianStoppedIncrement μ v a N (t i) K (N-(j.val+1)) (x i)-
      (1/Real.sqrt (N : ℝ) : ℝ) • gaussianTruncatedStoppedIncrement μ v a N (t i) K R j.rev.val (x i) = _
  rw [Fin.val_rev]
  exact (smul_sub _ _ _).symm

/-- Exact normalized Frobenius identity for the actual discarded matrix. -/
lemma gaussianMatrixTruncationError_norm_sq (μ : Measure 𝕂) [SFinite μ]
    (v : ℕ → 𝕂) (a : ℝ) (t : Fin N → 𝕂) (K R : ℝ)
    (x : Fin N → Fin N → 𝕂 × 𝕂) :
    ‖gaussianMatrixTruncationError μ v a t K R x‖^2 =
      (1/(N : ℝ))*(∑ i, ∑ j : Fin N,
        ‖gaussianStoppedTruncationError μ v a N (t i) K R (N-(j.val+1)) (x i)‖^2) := by
  rw [frobenius_norm_sq_eq_sum]
  simp only [gaussianMatrixTruncationError_apply, norm_smul, Real.norm_eq_abs, mul_pow,
    sq_abs, div_pow, one_pow, Real.sq_sqrt (Nat.cast_nonneg N), Finset.mul_sum]

#print axioms gaussianMatrixTruncationError_norm_sq
end SpectralRadiusUpperTail

import SpectralRadiusUpperTail.GaussianMatrixMartingale
import SpectralRadiusUpperTail.FiniteArraySum
import SpectralRadiusUpperTail.ActualMatrixIdentity

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators Matrix.Norms.Frobenius
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂] {N : ℕ}

/-- The actual normalized stopped and conditionally recentered matrix, in
the original column coordinates. -/
noncomputable def gaussianTruncatedMatrix (μ : Measure 𝕂) [SFinite μ]
    (v : ℕ → 𝕂) (a : ℝ) (t : Fin N → 𝕂) (K R : ℝ)
    (x : Fin N → Fin N → 𝕂 × 𝕂) : Matrix (Fin N) (Fin N) 𝕂 :=
  normalizedArray (fun i j => gaussianMatrixTruncatedEntry μ v a t K R i j.rev.val x)

lemma gaussianMatrixCoordinateIncrement_apply (μ : Measure 𝕂) [SFinite μ]
    (v : ℕ → 𝕂) (a : ℝ) (t : Fin N → 𝕂) (K R : ℝ) (i n p q : Fin N)
    (x : Fin N → Fin N → 𝕂 × 𝕂) :
    gaussianMatrixCoordinateIncrement μ v a t K R i n x p q =
      if p=i ∧ q=n.rev then (Real.sqrt (N : ℝ))⁻¹ • gaussianMatrixTruncatedEntry μ v a t K R i n.val x
        else 0 := by
  change (Real.sqrt (N : ℝ))⁻¹ •
    (matrixCoordinateL i n.rev (gaussianMatrixTruncatedEntry μ v a t K R i n.val x) p q) = _
  rw [matrixCoordinateL_apply]
  split_ifs <;> simp only [smul_zero]

/-- The terminal value of the checked matrix martingale is exactly the
actual truncated matrix, including the descending-to-original column reversal. -/
theorem gaussianTruncatedMatrix_terminal_sum (μ : Measure 𝕂) [SFinite μ]
    (v : ℕ → 𝕂) (a : ℝ) (t : Fin N → 𝕂) (K R : ℝ)
    (x : Fin N → Fin N → 𝕂 × 𝕂) :
    incrementPartialSum (finiteArrayIncrement (gaussianMatrixCoordinateIncrement μ v a t K R))
      (N*N) x = gaussianTruncatedMatrix μ v a t K R x := by
  rw [finiteArray_terminal_sum]
  funext p q
  have heq (n : Fin N) : q=n.rev ↔ n=q.rev := by
    constructor
    · intro h
      simpa only [Fin.rev_rev] using (congrArg Fin.rev h).symm
    · intro h
      simpa only [Fin.rev_rev] using (congrArg Fin.rev h).symm
  simp only [Finset.sum_apply, gaussianMatrixCoordinateIncrement_apply, heq]
  simp only [ite_and]
  simp [gaussianTruncatedMatrix, normalizedArray, one_div]

#print axioms gaussianTruncatedMatrix_terminal_sum
end SpectralRadiusUpperTail

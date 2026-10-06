import SpectralRadiusUpperTail.GaussianMatrixMartingale
import SpectralRadiusUpperTail.MatrixCoordinateNorm

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped Matrix.Norms.Frobenius
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂] {N : ℕ}

/-- The actual normalized matrix-unit increment has Euclidean operator norm
at most 2R/sqrt(N), under the same stopping and conditional recentering. -/
theorem gaussianMatrixCoordinateIncrement_operator_norm_le
    (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (v : ℕ → 𝕂) (a : ℝ) (ha : 0 < a)
    (t : Fin N → 𝕂) (K R : ℝ) (hR : 0 ≤ R) (i n : Fin N)
    (x : Fin N → Fin N → 𝕂 × 𝕂) :
    ‖Matrix.toEuclideanCLM (n := Fin N) (𝕜 := 𝕂)
      (gaussianMatrixCoordinateIncrement μ v a t K R i n x)‖ ≤ 2*R/Real.sqrt (N : ℝ) := by
  have hc : 0 ≤ (Real.sqrt (N : ℝ))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  calc
    _ ≤ (Real.sqrt (N : ℝ))⁻¹*‖gaussianMatrixTruncatedEntry μ v a t K R i n.val x‖ :=
      matrixCoordinate_scaled_operator_le i n.rev _ _ hc
    _ ≤ (Real.sqrt (N : ℝ))⁻¹*(2*R) := mul_le_mul_of_nonneg_left
      (gaussianMatrixTruncatedEntry_norm_le μ hX v a ha t K R hR i n.val x) hc
    _ = 2*R/Real.sqrt (N : ℝ) := by rw [div_eq_mul_inv, mul_comm]

theorem gaussianMatrixIncrement_operator_norm_le
    (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (v : ℕ → 𝕂) (a : ℝ) (ha : 0 < a)
    (t : Fin N → 𝕂) (K R : ℝ) (hR : 0 ≤ R) (r : ℕ)
    (x : Fin N → Fin N → 𝕂 × 𝕂) :
    ‖Matrix.toEuclideanCLM (n := Fin N) (𝕜 := 𝕂)
      (finiteArrayIncrement (gaussianMatrixCoordinateIncrement μ v a t K R) r x)‖ ≤
        2*R/Real.sqrt (N : ℝ) := by
  by_cases hr : r < N*N
  · let ij := finProdFinEquiv.symm (⟨r,hr⟩ : Fin (N*N))
    have he : finiteArrayIncrement (gaussianMatrixCoordinateIncrement μ v a t K R) r =
        gaussianMatrixCoordinateIncrement μ v a t K R ij.1 ij.2 := by
      rw [finiteArrayIncrement, dif_pos hr]
    have hn := congrArg (fun f : (Fin N → Fin N → 𝕂 × 𝕂) → (Fin N → Fin N → 𝕂) =>
      ‖Matrix.toEuclideanCLM (n := Fin N) (𝕜 := 𝕂) (f x)‖) he
    exact hn.trans_le (gaussianMatrixCoordinateIncrement_operator_norm_le μ hX v a ha t K R hR _ _ x)
  · have he : finiteArrayIncrement (gaussianMatrixCoordinateIncrement μ v a t K R) r = 0 := by
      rw [finiteArrayIncrement, dif_neg hr]
    have hn := congrArg (fun f : (Fin N → Fin N → 𝕂 × 𝕂) → (Fin N → Fin N → 𝕂) =>
      ‖Matrix.toEuclideanCLM (n := Fin N) (𝕜 := 𝕂) (f x)‖) he
    have hz : ‖Matrix.toEuclideanCLM (n := Fin N) (𝕜 := 𝕂)
        (0 : Matrix (Fin N) (Fin N) 𝕂)‖ = 0 := by simp
    exact (hn.trans hz).trans_le (by positivity)

#print axioms gaussianMatrixIncrement_operator_norm_le
end SpectralRadiusUpperTail

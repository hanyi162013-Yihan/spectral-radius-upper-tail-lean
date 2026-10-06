import SpectralRadiusUpperTail.GaussianHermitianVarianceSum
import SpectralRadiusUpperTail.HermitianCoordinateNorm
import SpectralRadiusUpperTail.GaussianMatrixTerminalSum
import SpectralRadiusUpperTail.FiniteArrayTimeSum

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped MeasureTheory BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂] {N : ℕ}

theorem gaussianHermitianCoordinateIncrement_operator_le
    (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (v : ℕ → 𝕂) (a : ℝ) (ha : 0 < a)
    (t : Fin N → 𝕂) (K R : ℝ) (hR : 0 ≤ R) (i n : Fin N)
    (x : Fin N → Fin N → 𝕂 × 𝕂) :
    ‖Matrix.toEuclideanCLM (n := Fin N ⊕ Fin N) (𝕜 := 𝕂)
      (gaussianHermitianCoordinateIncrement μ v a t K R i n x)‖ ≤ 2*R/Real.sqrt (N : ℝ) := by
  have hc : 0 ≤ (Real.sqrt (N : ℝ))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  change ‖Matrix.toEuclideanCLM (n := Fin N ⊕ Fin N) (𝕜 := 𝕂)
    (hermitianDilationL (gaussianMatrixCoordinateIncrement μ v a t K R i n x))‖ ≤ _
  rw [hermitianDilationL_apply]
  have hh := hermitian_scaled_matrixCoordinate_operator_le i n.rev
    (gaussianMatrixTruncatedEntry μ v a t K R i n.val x) (Real.sqrt (N : ℝ))⁻¹ hc
  apply hh.trans
  calc
    _ ≤ (Real.sqrt (N : ℝ))⁻¹*(2*R) := mul_le_mul_of_nonneg_left
      (gaussianMatrixTruncatedEntry_norm_le μ hX v a ha t K R hR i n.val x) hc
    _ = _ := by rw [div_eq_mul_inv, mul_comm]

theorem gaussianHermitianIncrement_operator_le
    (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (v : ℕ → 𝕂) (a : ℝ) (ha : 0 < a)
    (t : Fin N → 𝕂) (K R : ℝ) (hR : 0 ≤ R) (r : ℕ)
    (x : Fin N → Fin N → 𝕂 × 𝕂) :
    ‖Matrix.toEuclideanCLM (n := Fin N ⊕ Fin N) (𝕜 := 𝕂)
      (finiteArrayIncrement (E := ((Fin N ⊕ Fin N) → (Fin N ⊕ Fin N) → 𝕂)) (gaussianHermitianCoordinateIncrement μ v a t K R) r x)‖ ≤
        2*R/Real.sqrt (N : ℝ) := by
  by_cases hr : r < N*N
  · let ij := finProdFinEquiv.symm (⟨r,hr⟩ : Fin (N*N))
    have he : finiteArrayIncrement (E := ((Fin N ⊕ Fin N) → (Fin N ⊕ Fin N) → 𝕂)) (gaussianHermitianCoordinateIncrement μ v a t K R) r =
        gaussianHermitianCoordinateIncrement μ v a t K R ij.1 ij.2 := by
      rw [finiteArrayIncrement, dif_pos hr]
    have hn := congrArg (fun f : (Fin N → Fin N → 𝕂 × 𝕂) →
        ((Fin N ⊕ Fin N) → (Fin N ⊕ Fin N) → 𝕂) =>
      ‖Matrix.toEuclideanCLM (n := Fin N ⊕ Fin N) (𝕜 := 𝕂) (f x)‖) he
    exact hn.trans_le (gaussianHermitianCoordinateIncrement_operator_le μ hX v a ha t K R hR _ _ x)
  · have he : finiteArrayIncrement (E := ((Fin N ⊕ Fin N) → (Fin N ⊕ Fin N) → 𝕂)) (gaussianHermitianCoordinateIncrement μ v a t K R) r = 0 := by
      rw [finiteArrayIncrement, dif_neg hr]
    have hn := congrArg (fun f : (Fin N → Fin N → 𝕂 × 𝕂) →
        ((Fin N ⊕ Fin N) → (Fin N ⊕ Fin N) → 𝕂) =>
      ‖Matrix.toEuclideanCLM (n := Fin N ⊕ Fin N) (𝕜 := 𝕂) (f x)‖) he
    have hz : ‖Matrix.toEuclideanCLM (n := Fin N ⊕ Fin N) (𝕜 := 𝕂)
        (0 : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) 𝕂)‖ = 0 := by simp
    exact (hn.trans hz).trans_le (by positivity)

/-- The terminal sum is the actual dilation of the actual truncated matrix. -/
theorem gaussianHermitian_terminal_sum (μ : Measure 𝕂) [SFinite μ]
    (v : ℕ → 𝕂) (a : ℝ) (t : Fin N → 𝕂) (K R : ℝ)
    (x : Fin N → Fin N → 𝕂 × 𝕂) :
    incrementPartialSum (finiteArrayIncrement (E := ((Fin N ⊕ Fin N) → (Fin N ⊕ Fin N) → 𝕂)) (gaussianHermitianCoordinateIncrement μ v a t K R))
      (N*N) x = hermitianDilation (gaussianTruncatedMatrix μ v a t K R x) := by
  rw [finiteArray_terminal_sum]
  calc
    _ = hermitianDilationL (∑ i, ∑ n, gaussianMatrixCoordinateIncrement μ v a t K R i n x) := by
      simp only [map_sum, gaussianHermitianCoordinateIncrement, Function.comp_apply]
    _ = _ := by
      rw [← finiteArray_terminal_sum, gaussianTruncatedMatrix_terminal_sum]
      exact hermitianDilationL_apply _

/-- The predictable variance process of the actual serialized increments. -/
noncomputable def gaussianHermitianPredictableVariance (μ : Measure 𝕂) [SFinite μ]
    (v : ℕ → 𝕂) (a : ℝ) (t : Fin N → 𝕂) (K R : ℝ) (r : ℕ)
    (x : Fin N → Fin N → 𝕂 × 𝕂) : (Fin N ⊕ Fin N) → (Fin N ⊕ Fin N) → 𝕂 :=
  ∑ k ∈ Finset.range r, MeasureTheory.condExp
    (E := ((Fin N ⊕ Fin N) → (Fin N ⊕ Fin N) → 𝕂))
    (rowMajorFiltration N N k) (gaussianSequentialMatrixLaw μ v a t)
    (fun y => matrixSelfProduct (finiteArrayIncrement
      (E := ((Fin N ⊕ Fin N) → (Fin N ⊕ Fin N) → 𝕂))
      (gaussianHermitianCoordinateIncrement μ v a t K R) k y)) x

lemma gaussianHermitianPredictableVariance_terminal (μ : Measure 𝕂) [SFinite μ]
    (v : ℕ → 𝕂) (a : ℝ) (t : Fin N → 𝕂) (K R : ℝ)
    (x : Fin N → Fin N → 𝕂 × 𝕂) :
    gaussianHermitianPredictableVariance μ v a t K R (N*N) x =
      gaussianHermitianVarianceSum μ v a t K R x := by
  unfold gaussianHermitianPredictableVariance
  rw [finiteArray_time_sum]
  simp_rw [finiteArrayIncrement_at]
  rfl

#print axioms gaussianHermitian_terminal_sum
#print axioms gaussianHermitianPredictableVariance_terminal
end SpectralRadiusUpperTail

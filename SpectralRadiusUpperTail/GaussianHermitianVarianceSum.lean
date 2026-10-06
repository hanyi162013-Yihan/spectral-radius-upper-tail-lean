import SpectralRadiusUpperTail.GaussianHermitianVariance
import SpectralRadiusUpperTail.DilationVarianceSum

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped MeasureTheory BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂] {N : ℕ}

/-- Sum of the actual conditional squared Hermitian increments, each
conditioned on its own preceding full-matrix history. -/
noncomputable def gaussianHermitianVarianceSum (μ : Measure 𝕂) [SFinite μ]
    (v : ℕ → 𝕂) (a : ℝ) (t : Fin N → 𝕂) (K R : ℝ)
    (x : Fin N → Fin N → 𝕂 × 𝕂) : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) 𝕂 :=
  ∑ i, ∑ n, (gaussianSequentialMatrixLaw μ v a t)[
    gaussianHermitianCoordinateSquare μ v a t K R i n |
      rowMajorFiltration N N (i.val*N+n.val)] x

/-- Both variance blocks are bounded on the actual coupling by the
coefficient envelope times the explicit scalar conditional-variance cost. -/
theorem gaussianHermitianVarianceSum_operator_le
    (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (hm : (∫ x : 𝕂, x ∂μ) = 0)
    (hvar : (∫ x : 𝕂, ‖x‖^2 ∂μ) = 1) (v : ℕ → 𝕂)
    (hv : ∑ j : Fin N, ‖v j.val‖^2 ≤ 1) (a d : ℝ) (ha : 0 < a) (hd : 0 < d)
    (hexp : Integrable (fun x : 𝕂 => Real.exp (4*d*‖x‖^2)) μ)
    (t : Fin N → 𝕂) (K δ R : ℝ) (hK : 0 ≤ K) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1) (hR : 0 ≤ R)
    (hb : ∀ j : Fin N, ‖v j.val‖ ≤ δ)
    (hunit : gaussianTruncationScale μ a d K*δ ≤ 1)
    (herror : (gaussianTruncationScale μ a d K*δ)*gaussianLocalMomentCost μ d ≤ 1/2) :
    ∀ᵐ x ∂gaussianSequentialMatrixLaw μ v a t,
      ‖Matrix.toEuclideanCLM (n := Fin N ⊕ Fin N) (𝕜 := 𝕂)
        (gaussianHermitianVarianceSum μ v a t K R x)‖ ≤
          (12*gaussianTruncationScale μ a d K*gaussianLocalMomentCost μ d)*δ := by
  let P := gaussianSequentialMatrixLaw μ v a t
  let C := 12*gaussianTruncationScale μ a d K*gaussianLocalMomentCost μ d
  let w (i n : Fin N) := P[(fun y => ‖gaussianMatrixTruncatedEntry μ v a t K R i n.val y‖^2) |
    rowMajorFiltration N N (i.val*N+n.val)]
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg (by norm_num)
    (gaussianTruncationScale_nonneg μ a d K ha hd hK)) (gaussianLocalMomentCost_nonneg μ d hd.le)
  have he : ∀ᵐ x ∂P, ∀ i n : Fin N,
      P[gaussianHermitianCoordinateSquare μ v a t K R i n |
        rowMajorFiltration N N (i.val*N+n.val)] x =
          ((N : ℝ)⁻¹ • dilationVarianceCoordinateL (𝕂 := 𝕂) i n.rev) (w i n x) := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro n
    exact (gaussianHermitianCoordinateSquare_condExp μ hX v a ha t K R hR i n).2
  have hw0 : ∀ᵐ x ∂P, ∀ i n : Fin N, 0 ≤ w i n x := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro n
    exact condExp_nonneg (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
  have hw : ∀ᵐ x ∂P, ∀ i n : Fin N, w i n x ≤ C*δ := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro n
    have hbn : ‖v (N-(n.val+1))‖ ≤ δ := by simpa only [Fin.val_rev] using hb n.rev
    have hh := gaussianMatrixTruncatedEntry_conditional_variance_le μ hX hm hvar v hv a d ha hd
      hexp t i n.val n.isLt K δ R hK hδ hR hbn hunit herror
    filter_upwards [hh] with x hx
    exact hx.trans (mul_le_mul_of_nonneg_left hbn hC)
  filter_upwards [he, hw0, hw] with x hx hx0 hxb
  have hs : gaussianHermitianVarianceSum μ v a t K R x =
      (N : ℝ)⁻¹ • (∑ i, ∑ n, dilationVarianceCoordinateL (𝕂 := 𝕂) i n.rev (w i n x)) := by
    unfold gaussianHermitianVarianceSum
    change (∑ i, ∑ n, P[gaussianHermitianCoordinateSquare μ v a t K R i n |
      rowMajorFiltration N N (i.val*N+n.val)] x) = _
    simp_rw [hx]
    simp only [ContinuousLinearMap.smul_apply, Finset.smul_sum]
  rw [hs]
  exact dilationVarianceCoordinate_sum_operator_le (fun i n => w i n x) (C*δ)
    (mul_nonneg hC hδ0) hx0 hxb

#print axioms gaussianHermitianVarianceSum_operator_le
end SpectralRadiusUpperTail

import SpectralRadiusUpperTail.GaussianHermitianNormalizedVariance

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped MeasureTheory Matrix.Norms.L2Operator
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂] {N : ℕ}
attribute [local instance] matrixL2RealNormedAlgebra

/-- Normalized actual total predictable variance inherits the proved coupling bound. -/
theorem gaussianHermitianUnit_variance_le
    (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (hm : (∫ x : 𝕂, x ∂μ) = 0)
    (hvar : (∫ x : 𝕂, ‖x‖^2 ∂μ) = 1) (v : ℕ → 𝕂)
    (hv : ∑ j : Fin N, ‖v j.val‖^2 ≤ 1) (a d : ℝ) (ha : 0 < a) (hd : 0 < d)
    (hexp : Integrable (fun x : 𝕂 => Real.exp (4*d*‖x‖^2)) μ)
    (t : Fin N → 𝕂) (K δ R : ℝ) (hK : 0 ≤ K) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1) (hR : 0 ≤ R)
    (hb : ∀ j : Fin N, ‖v j.val‖ ≤ δ)
    (hunit : gaussianTruncationScale μ a d K*δ ≤ 1)
    (herror : (gaussianTruncationScale μ a d K*δ)*gaussianLocalMomentCost μ d ≤ 1/2) (b : ℝ) :
    let P := gaussianSequentialMatrixLaw μ v a t
    ∀ᵐ x ∂P, ‖∑ i ∈ Finset.range (N*N), P[fun y =>
      (gaussianHermitianUnitIncrement μ v a t K R b i y)^2 | rowMajorFiltration N N i] x‖ ≤
        b⁻¹^2 * ((12*gaussianTruncationScale μ a d K*gaussianLocalMomentCost μ d)*δ) := by
  have he := gaussianHermitianUnit_variance_sum μ hX v a ha t K R hR b (N*N)
  have hvb := gaussianHermitianVarianceSum_operator_le μ hX hm hvar v hv a d ha hd
    hexp t K δ R hK hδ0 hδ hR hb hunit herror
  filter_upwards [he, hvb] with x hx hy
  rw [hx, gaussianHermitianPredictableVariance_terminal, norm_smul,
    Real.norm_of_nonneg (sq_nonneg b⁻¹)]
  exact mul_le_mul_of_nonneg_left hy (sq_nonneg b⁻¹)

#print axioms gaussianHermitianUnit_variance_le
end SpectralRadiusUpperTail

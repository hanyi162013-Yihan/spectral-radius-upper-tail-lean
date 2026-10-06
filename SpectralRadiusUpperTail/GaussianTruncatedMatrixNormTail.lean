import SpectralRadiusUpperTail.GaussianHermitianSumNormTail
import SpectralRadiusUpperTail.GaussianHermitianNormalizedTerminal
import SpectralRadiusUpperTail.HermitianDilationOperator

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped MeasureTheory Matrix.Norms.L2Operator ComplexOrder MatrixOrder
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂] {N : ℕ}
attribute [local instance] matrixL2RealNormedAlgebra

/-- Actual truncated coupling error has an operator-norm tail, with the explicit
4N factor from the two spectral sides of its Hermitian dilation. -/
theorem gaussianTruncatedMatrix_norm_tail [NeZero N]
    (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (hm : (∫ x : 𝕂, x ∂μ) = 0)
    (hvar : (∫ x : 𝕂, ‖x‖^2 ∂μ) = 1) (v : ℕ → 𝕂)
    (hv : ∑ j : Fin N, ‖v j.val‖^2 ≤ 1) (a d : ℝ) (ha : 0 < a) (hd : 0 < d)
    (hexp : Integrable (fun x : 𝕂 => Real.exp (4*d*‖x‖^2)) μ)
    (t : Fin N → 𝕂) (K δ R : ℝ) (hK : 0 ≤ K) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1) (hR : 0 ≤ R)
    (hb : ∀ j : Fin N, ‖v j.val‖ ≤ δ)
    (hunit : gaussianTruncationScale μ a d K*δ ≤ 1)
    (herror : (gaussianTruncationScale μ a d K*δ)*gaussianLocalMomentCost μ d ≤ 1/2) (b : ℝ) (hb0 : 0 < b)
    (hbnd : 2*R/Real.sqrt (N : ℝ) ≤ b) (s u : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1/2) :
    let P := gaussianSequentialMatrixLaw μ v a t
    P.real {x | u ≤ ‖Matrix.toEuclideanCLM (n := Fin N) (𝕜 := 𝕂)
      (gaussianTruncatedMatrix μ v a t K R x)‖} ≤
      (4*(N : ℝ))*Real.exp (-s*(b⁻¹*u)+2*s^2*(b⁻¹^2 *
        ((12*gaussianTruncationScale μ a d K*gaussianLocalMomentCost μ d)*δ))) := by
  have : IsProbabilityMeasure (gaussianSequentialMatrixLaw μ v a t) :=
    gaussianSequentialMatrixLaw_probability μ v a ha t
  have ht := gaussianHermitianUnit_sum_norm_tail μ hX hm hvar v hv a d ha hd hexp
    t K δ R hK hδ0 hδ hR hb hunit herror b hb0 hbnd s (b⁻¹*u) hs hs1
  have hsub : {x | u ≤ ‖Matrix.toEuclideanCLM (n := Fin N) (𝕜 := 𝕂)
      (gaussianTruncatedMatrix μ v a t K R x)‖} ⊆
      {x | b⁻¹*u ≤ ‖∑ i ∈ Finset.range (N*N),
        gaussianHermitianUnitIncrement μ v a t K R b i x‖} := by
    intro x hx
    change b⁻¹*u ≤ ‖∑ i ∈ Finset.range (N*N),
      gaussianHermitianUnitIncrement μ v a t K R b i x‖
    rw [gaussianHermitianUnit_terminal_sum, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr hb0.le)]
    exact mul_le_mul_of_nonneg_left
      (hx.trans (euclidean_operator_le_hermitianDilation _)) (inv_nonneg.mpr hb0.le)
  exact (measureReal_mono hsub).trans ht

#print axioms gaussianTruncatedMatrix_norm_tail
end SpectralRadiusUpperTail

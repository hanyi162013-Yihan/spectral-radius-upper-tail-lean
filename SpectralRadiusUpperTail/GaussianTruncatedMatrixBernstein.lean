import SpectralRadiusUpperTail.GaussianTruncatedMatrixNormTail
import SpectralRadiusUpperTail.ScaledBernsteinParameter

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped MeasureTheory Matrix.Norms.L2Operator ComplexOrder MatrixOrder
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂] {N : ℕ}
attribute [local instance] matrixL2RealNormedAlgebra

/-- Explicit optimized norm concentration for the actual truncated coupling error. -/
theorem gaussianTruncatedMatrix_bernstein [NeZero N]
    (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (hm : (∫ x : 𝕂, x ∂μ) = 0)
    (hvar : (∫ x : 𝕂, ‖x‖^2 ∂μ) = 1) (v : ℕ → 𝕂)
    (hv : ∑ j : Fin N, ‖v j.val‖^2 ≤ 1) (a d : ℝ) (ha : 0 < a) (hd : 0 < d)
    (hexp : Integrable (fun x : 𝕂 => Real.exp (4*d*‖x‖^2)) μ)
    (t : Fin N → 𝕂) (K δ R : ℝ) (hK : 0 ≤ K) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1) (hR : 0 ≤ R)
    (hb : ∀ j : Fin N, ‖v j.val‖ ≤ δ)
    (hunit : gaussianTruncationScale μ a d K*δ ≤ 1)
    (herror : (gaussianTruncationScale μ a d K*δ)*gaussianLocalMomentCost μ d ≤ 1/2) (b : ℝ) (hb0 : 0 < b)
    (hbnd : 2*R/Real.sqrt (N : ℝ) ≤ b) (u : ℝ) (hu : 0 < u) :
    let P := gaussianSequentialMatrixLaw μ v a t
    P.real {x | u ≤ ‖Matrix.toEuclideanCLM (n := Fin N) (𝕜 := 𝕂)
      (gaussianTruncatedMatrix μ v a t K R x)‖} ≤
      (4*(N : ℝ))*Real.exp (-u^2/(8*
        ((12*gaussianTruncationScale μ a d K*gaussianLocalMomentCost μ d)*δ)+4*b*u)) := by
  have hV : 0 ≤ (12*gaussianTruncationScale μ a d K*gaussianLocalMomentCost μ d)*δ := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
      (gaussianTruncationScale_nonneg μ a d K ha hd hK))
      (gaussianLocalMomentCost_nonneg μ d hd.le)) hδ0
  obtain ⟨s, hs, hs1, he⟩ := scaled_bernstein_parameter hV hb0 hu
  have ht := gaussianTruncatedMatrix_norm_tail μ hX hm hvar v hv a d ha hd hexp
    t K δ R hK hδ0 hδ hR hb hunit herror b hb0 hbnd s u hs hs1
  exact ht.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he)
    (mul_nonneg (by norm_num) (Nat.cast_nonneg N)))

#print axioms gaussianTruncatedMatrix_bernstein
end SpectralRadiusUpperTail

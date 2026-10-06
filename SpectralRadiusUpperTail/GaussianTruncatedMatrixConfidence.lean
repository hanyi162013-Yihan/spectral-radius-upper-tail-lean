import SpectralRadiusUpperTail.GaussianTruncatedMatrixBernstein
import SpectralRadiusUpperTail.BernsteinThreshold

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped MeasureTheory Matrix.Norms.L2Operator ComplexOrder MatrixOrder
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂] {N : ℕ}
attribute [local instance] matrixL2RealNormedAlgebra

/-- Explicit threshold bound on the actual coupling, with no assumed concentration input. -/
theorem gaussianTruncatedMatrix_confidence [NeZero N]
    (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (hm : (∫ x : 𝕂, x ∂μ) = 0)
    (hvar : (∫ x : 𝕂, ‖x‖^2 ∂μ) = 1) (v : ℕ → 𝕂)
    (hv : ∑ j : Fin N, ‖v j.val‖^2 ≤ 1) (a d : ℝ) (ha : 0 < a) (hd : 0 < d)
    (hexp : Integrable (fun x : 𝕂 => Real.exp (4*d*‖x‖^2)) μ)
    (t : Fin N → 𝕂) (K δ R : ℝ) (hK : 0 ≤ K) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1) (hR : 0 ≤ R)
    (hb : ∀ j : Fin N, ‖v j.val‖ ≤ δ)
    (hunit : gaussianTruncationScale μ a d K*δ ≤ 1)
    (herror : (gaussianTruncationScale μ a d K*δ)*gaussianLocalMomentCost μ d ≤ 1/2) (b : ℝ) (hb0 : 0 < b)
    (hbnd : 2*R/Real.sqrt (N : ℝ) ≤ b) (L : ℝ) (hL : 0 < L) :
    let P := gaussianSequentialMatrixLaw μ v a t
    let V := (12*gaussianTruncationScale μ a d K*gaussianLocalMomentCost μ d)*δ
    P.real {x | 4*Real.sqrt (V*L)+8*b*L ≤ ‖Matrix.toEuclideanCLM (n := Fin N) (𝕜 := 𝕂)
      (gaussianTruncatedMatrix μ v a t K R x)‖} ≤ (4*(N : ℝ))*Real.exp (-L) := by
  let V := (12*gaussianTruncationScale μ a d K*gaussianLocalMomentCost μ d)*δ
  have hV : 0 ≤ V := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
    (gaussianTruncationScale_nonneg μ a d K ha hd hK))
    (gaussianLocalMomentCost_nonneg μ d hd.le)) hδ0
  have hh := bernstein_threshold hV hb0 hL
  have ht := gaussianTruncatedMatrix_bernstein μ hX hm hvar v hv a d ha hd hexp
    t K δ R hK hδ0 hδ hR hb hunit herror b hb0 hbnd
    (4*Real.sqrt (V*L)+8*b*L) hh.1
  exact ht.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hh.2)
    (mul_nonneg (by norm_num) (Nat.cast_nonneg N)))

#print axioms gaussianTruncatedMatrix_confidence
end SpectralRadiusUpperTail

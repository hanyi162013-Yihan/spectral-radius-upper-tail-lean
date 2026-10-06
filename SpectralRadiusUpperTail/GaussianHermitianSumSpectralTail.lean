import SpectralRadiusUpperTail.GaussianHermitianNormalizedVarianceBound
import SpectralRadiusUpperTail.MatrixMartingaleSpectralTail

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped MeasureTheory Matrix.Norms.L2Operator ComplexOrder MatrixOrder
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂] {N : ℕ}
attribute [local instance] matrixL2RealNormedAlgebra

/-- Actual Gaussian-soft increment-sum spectral tail: the variance hypothesis is discharged
by the proved coupling variance estimate, under its original entry assumptions. -/
theorem gaussianHermitianUnit_sum_spectral_tail [NeZero N]
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
    P.real {x | ∃ l ∈ spectrum ℝ
      (∑ i ∈ Finset.range (N*N), gaussianHermitianUnitIncrement μ v a t K R b i x), u ≤ l} ≤
      (2*(N : ℝ))*Real.exp (-s*u+2*s^2*(b⁻¹^2 *
        ((12*gaussianTruncationScale μ a d K*gaussianLocalMomentCost μ d)*δ))) := by
  have : IsProbabilityMeasure (gaussianSequentialMatrixLaw μ v a t) :=
    gaussianSequentialMatrixLaw_probability μ v a ha t
  have hg := gaussianHermitianUnitIncrement_basics μ hX v a ha t K R hR b hb0 hbnd
  have hvb := gaussianHermitianUnit_variance_le μ hX hm hvar v hv a d ha hd
    hexp t K δ R hK hδ0 hδ hR hb hunit herror b
  have ht := matrix_martingale_spectral_tail (rowMajorFiltration N N)
    (gaussianHermitianUnitIncrement μ v a t K R b)
    (fun i => (hg i).1) (fun i => (hg i).2.1) (fun i => (hg i).2.2.1)
    (fun i => (hg i).2.2.2) hs hs1 (N*N) u _ hvb
  simpa only [Fintype.card_sum, Fintype.card_fin, Nat.cast_add, two_mul] using ht

#print axioms gaussianHermitianUnit_sum_spectral_tail
end SpectralRadiusUpperTail

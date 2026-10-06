import SpectralRadiusUpperTail.GaussianHermitianStateTrace
import SpectralRadiusUpperTail.MatrixCompensatedSpectralTail

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped MeasureTheory MatrixOrder Matrix.Norms.L2Operator ComplexOrder
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂] {N : ℕ}
attribute [local instance] matrixL2RealNormedAlgebra

/-- Spectral tail for the actual Gaussian-soft compensated process. -/
theorem gaussianHermitianState_spectral_tail [NeZero N]
    (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (v : ℕ → 𝕂) (a : ℝ) (ha : 0 < a)
    (t : Fin N → 𝕂) (K R : ℝ) (hR : 0 ≤ R) (b : ℝ) (hb : 0 < b)
    (hbnd : 2*R/Real.sqrt (N : ℝ) ≤ b) (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1/2)
    (n : ℕ) (u : ℝ) :
    let P := gaussianSequentialMatrixLaw μ v a t
    let X := gaussianHermitianUnitIncrement μ v a t K R b
    P.real {x | ∃ l ∈ spectrum ℝ
      (matrixCompensatedState P (rowMajorFiltration N N) X s n x), u ≤ l} ≤
        (2*(N : ℝ))*Real.exp (-u) := by
  have : IsProbabilityMeasure (gaussianSequentialMatrixLaw μ v a t) :=
    gaussianSequentialMatrixLaw_probability μ v a ha t
  have hg := gaussianHermitianUnitIncrement_basics μ hX v a ha t K R hR b hb hbnd
  have ht := matrixCompensatedState_spectral_tail (rowMajorFiltration N N)
    (gaussianHermitianUnitIncrement μ v a t K R b)
    (fun r => (hg r).1) (fun r => (hg r).2.1)
    (fun r => (hg r).2.2.1) (fun r => (hg r).2.2.2) hs hs1 n u
  simpa only [Fintype.card_sum, Fintype.card_fin, Nat.cast_add, two_mul] using ht

#print axioms gaussianHermitianState_spectral_tail
end SpectralRadiusUpperTail

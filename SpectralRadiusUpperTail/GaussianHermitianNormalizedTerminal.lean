import SpectralRadiusUpperTail.GaussianHermitianExponential

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped MeasureTheory Matrix.Norms.L2Operator
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂] {N : ℕ}
attribute [local instance] matrixL2RealNormedAlgebra

/-- Terminal sum of normalized actual increments equals the scaled Hermitian dilation. -/
theorem gaussianHermitianUnit_terminal_sum (μ : Measure 𝕂) [SFinite μ]
    (v : ℕ → 𝕂) (a : ℝ) (t : Fin N → 𝕂) (K R b : ℝ)
    (x : Fin N → Fin N → 𝕂 × 𝕂) :
    (∑ i ∈ Finset.range (N*N), gaussianHermitianUnitIncrement μ v a t K R b i x) =
      b⁻¹ • matrixL2Equiv (hermitianDilation (gaussianTruncatedMatrix μ v a t K R x)) := by
  rw [← gaussianHermitian_terminal_sum μ v a t K R x]
  simp only [incrementPartialSum, gaussianHermitianUnitIncrement, map_sum, Finset.smul_sum]

#print axioms gaussianHermitianUnit_terminal_sum
end SpectralRadiusUpperTail

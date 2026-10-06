import SpectralRadiusUpperTail.GaussianHermitianStateTrace
import SpectralRadiusUpperTail.MatrixRescaledConditionalSquare

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped MeasureTheory Matrix.Norms.L2Operator
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂] {N : ℕ}
attribute [local instance] matrixL2RealNormedAlgebra

/-- Square integrability for every serialized raw increment, including zero continuation. -/
lemma gaussianHermitianSerialized_square_integrable (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (v : ℕ → 𝕂) (a : ℝ) (ha : 0 < a)
    (t : Fin N → 𝕂) (K R : ℝ) (hR : 0 ≤ R) (r : ℕ) :
    Integrable (ε := (Fin N ⊕ Fin N) → (Fin N ⊕ Fin N) → 𝕂) (fun x => (matrixSelfProduct (finiteArrayIncrement
      (E := ((Fin N ⊕ Fin N) → (Fin N ⊕ Fin N) → 𝕂))
      (gaussianHermitianCoordinateIncrement μ v a t K R) r x) :
        (Fin N ⊕ Fin N) → (Fin N ⊕ Fin N) → 𝕂))
      (gaussianSequentialMatrixLaw μ v a t) := by
  apply finiteArrayIncrement_property (gaussianHermitianCoordinateIncrement μ v a t K R)
    (fun _ f => Integrable (ε := (Fin N ⊕ Fin N) → (Fin N ⊕ Fin N) → 𝕂) (fun x => (matrixSelfProduct (f x) :
      (Fin N ⊕ Fin N) → (Fin N ⊕ Fin N) → 𝕂)) (gaussianSequentialMatrixLaw μ v a t))
  · intro i j
    exact (gaussianHermitianCoordinateSquare_condExp μ hX v a ha t K R hR i j).1
  · intro j
    have hz : (fun x : Fin N → Fin N → 𝕂 × 𝕂 =>
        (matrixSelfProduct ((0 : (Fin N → Fin N → 𝕂 × 𝕂) →
          (Fin N ⊕ Fin N) → (Fin N ⊕ Fin N) → 𝕂) x) :
          (Fin N ⊕ Fin N) → (Fin N ⊕ Fin N) → 𝕂)) = 0 := by
      funext x
      exact Matrix.zero_mul _
    rw [hz]
    exact integrable_zero _ _ _

/-- The actual normalized predictable variance is exactly b^-2 times the raw variance,
with the conditional expectations transported between their Banach-space norms. -/
theorem gaussianHermitianUnit_variance_sum (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (v : ℕ → 𝕂) (a : ℝ) (ha : 0 < a)
    (t : Fin N → 𝕂) (K R : ℝ) (hR : 0 ≤ R) (b : ℝ) (n : ℕ) :
    let P := gaussianSequentialMatrixLaw μ v a t
    ∀ᵐ x ∂P, (∑ i ∈ Finset.range n, P[fun y =>
      (gaussianHermitianUnitIncrement μ v a t K R b i y)^2 | rowMajorFiltration N N i] x) =
        b⁻¹^2 • matrixL2Equiv (gaussianHermitianPredictableVariance μ v a t K R n x) := by
  let d := finiteArrayIncrement (E := ((Fin N ⊕ Fin N) → (Fin N ⊕ Fin N) → 𝕂))
    (gaussianHermitianCoordinateIncrement μ v a t K R)
  have he := fun i => matrix_rescaled_conditional_square (m := rowMajorFiltration N N i)
    (d i) b⁻¹ (gaussianHermitianSerialized_square_integrable μ hX v a ha t K R hR i)
  filter_upwards [ae_all_iff.mpr he] with x hx
  change (∑ i ∈ Finset.range n, _[fun y => (b⁻¹ • matrixL2Equiv (d i y))^2 |
    rowMajorFiltration N N i] x) = _
  rw [Finset.sum_congr rfl (fun i _ => hx i)]
  simp only [gaussianHermitianPredictableVariance, map_sum, Finset.smul_sum]
  rfl

#print axioms gaussianHermitianSerialized_square_integrable
#print axioms gaussianHermitianUnit_variance_sum
end SpectralRadiusUpperTail

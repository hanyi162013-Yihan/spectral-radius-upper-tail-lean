import SpectralRadiusUpperTail.GaussianHermitianProcess
import SpectralRadiusUpperTail.FiniteArrayProperty
import SpectralRadiusUpperTail.MatrixRescaledConditionalExponential

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped MeasureTheory MatrixOrder Matrix.Norms.L2Operator ComplexOrder
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂] {N : ℕ}
attribute [local instance] matrixL2RealNormedAlgebra

theorem gaussianHermitianSerialized_basics (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (v : ℕ → 𝕂) (a : ℝ) (ha : 0 < a)
    (t : Fin N → 𝕂) (K R : ℝ) (hR : 0 ≤ R) (r : ℕ) :
    let d := finiteArrayIncrement (E := ((Fin N ⊕ Fin N) → (Fin N ⊕ Fin N) → 𝕂))
      (gaussianHermitianCoordinateIncrement μ v a t K R)
    Integrable (d r) (gaussianSequentialMatrixLaw μ v a t) ∧
      (∀ x, Matrix.IsHermitian (d r x)) ∧
      (gaussianSequentialMatrixLaw μ v a t)[d r | rowMajorFiltration N N r]
        =ᵐ[gaussianSequentialMatrixLaw μ v a t] 0 := by
  apply finiteArrayIncrement_property
    (gaussianHermitianCoordinateIncrement μ v a t K R)
    (fun r f => Integrable f (gaussianSequentialMatrixLaw μ v a t) ∧
      (∀ x, Matrix.IsHermitian (f x)) ∧
      (gaussianSequentialMatrixLaw μ v a t)[f | rowMajorFiltration N N r]
        =ᵐ[gaussianSequentialMatrixLaw μ v a t] 0)
  · intro i n
    have hb := gaussianHermitianCoordinateIncrement_basics μ hX v a ha t K R hR i n
    exact ⟨hb.1, gaussianHermitianCoordinateIncrement_isHermitian μ v a t K R i n,
      hb.2.2⟩
  · intro r
    exact ⟨integrable_zero _ _ _, fun _ => Matrix.isHermitian_zero, by simp⟩

/-- The actual serialized increment, transported to operator norm and
scaled by a positive bound. The probability law is unchanged. -/
noncomputable def gaussianHermitianUnitIncrement (μ : Measure 𝕂) [SFinite μ]
    (v : ℕ → 𝕂) (a : ℝ) (t : Fin N → 𝕂) (K R b : ℝ) (r : ℕ)
    (x : Fin N → Fin N → 𝕂 × 𝕂) : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) 𝕂 :=
  b⁻¹ • matrixL2Equiv (finiteArrayIncrement
    (E := ((Fin N ⊕ Fin N) → (Fin N ⊕ Fin N) → 𝕂))
    (gaussianHermitianCoordinateIncrement μ v a t K R) r x)

/-- Instantiates the conditional matrix exponential inequality for
every time of the actual coupled matrix process, including zero continuation. -/
theorem gaussianHermitian_conditional_exp [NeZero N]
    (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (v : ℕ → 𝕂) (a : ℝ) (ha : 0 < a)
    (t : Fin N → 𝕂) (K R : ℝ) (hR : 0 ≤ R) (b : ℝ) (hb : 0 < b)
    (hbnd : 2*R/Real.sqrt (N : ℝ) ≤ b) (r : ℕ) (s : ℝ)
    (hs : 0 ≤ s) (hs1 : s ≤ 1/2) :
    let P := gaussianSequentialMatrixLaw μ v a t
    let X := gaussianHermitianUnitIncrement μ v a t K R b r
    let D := P[fun y => (X y)^2 | rowMajorFiltration N N r]
    let B := fun x => s • X x-(2*s^2) • D x
    Integrable (fun x => NormedSpace.exp (B x)) P ∧
      ∀ᵐ x ∂P, P[fun y => NormedSpace.exp (B y) | rowMajorFiltration N N r] x ≤ 1 := by
  have : IsProbabilityMeasure (gaussianSequentialMatrixLaw μ v a t) :=
    gaussianSequentialMatrixLaw_probability μ v a ha t
  have hg := gaussianHermitianSerialized_basics μ hX v a ha t K R hR r
  apply matrix_rescaled_conditional_exp ((rowMajorFiltration N N).le r) hg.1
    (.of_forall hg.2.1) hg.2.2 hb _ hs hs1
  exact .of_forall fun x =>
    (gaussianHermitianIncrement_operator_le μ hX v a ha t K R hR r x).trans hbnd

#print axioms gaussianHermitianSerialized_basics
#print axioms gaussianHermitian_conditional_exp
end SpectralRadiusUpperTail

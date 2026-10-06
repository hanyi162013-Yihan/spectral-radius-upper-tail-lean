import SpectralRadiusUpperTail.GaussianHermitianExponential
import SpectralRadiusUpperTail.MatrixCompensatedStateTrace

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped MeasureTheory MatrixOrder Matrix.Norms.L2Operator ComplexOrder
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂] {N : ℕ}
attribute [local instance] matrixL2RealNormedAlgebra

/-- The normalized increments are adapted, Hermitian, contractive and conditionally centered
under the actual Gaussian-soft coupling law. -/
theorem gaussianHermitianUnitIncrement_basics [NeZero N]
    (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (v : ℕ → 𝕂) (a : ℝ) (ha : 0 < a)
    (t : Fin N → 𝕂) (K R : ℝ) (hR : 0 ≤ R) (b : ℝ) (hb : 0 < b)
    (hbnd : 2*R/Real.sqrt (N : ℝ) ≤ b) (r : ℕ) :
    let P := gaussianSequentialMatrixLaw μ v a t
    let X := gaussianHermitianUnitIncrement μ v a t K R b r
    StronglyMeasurable[rowMajorFiltration N N (r+1)] X ∧
      (∀ᵐ x ∂P, (X x).IsHermitian) ∧ (∀ᵐ x ∂P, ‖X x‖ ≤ 1) ∧
      P[X | rowMajorFiltration N N r] =ᵐ[P] 0 := by
  have : IsProbabilityMeasure (gaussianSequentialMatrixLaw μ v a t) :=
    gaussianSequentialMatrixLaw_probability μ v a ha t
  let d := finiteArrayIncrement (E := ((Fin N ⊕ Fin N) → (Fin N ⊕ Fin N) → 𝕂))
    (gaussianHermitianCoordinateIncrement μ v a t K R)
  have hg := gaussianHermitianSerialized_basics μ hX v a ha t K R hR r
  have hd : StronglyMeasurable[rowMajorFiltration N N (r+1)] (d r) := by
    apply finiteArrayIncrement_property
      (gaussianHermitianCoordinateIncrement μ v a t K R)
      (fun j f => StronglyMeasurable[rowMajorFiltration N N (j+1)] f)
    · intro i j
      exact (gaussianHermitianCoordinateIncrement_basics μ hX v a ha t K R hR i j).2.1
    · intro j
      exact stronglyMeasurable_const
  let T : ((Fin N ⊕ Fin N) → (Fin N ⊕ Fin N) → 𝕂) →L[ℝ]
      Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) 𝕂 :=
    matrixL2Equiv.toContinuousLinearMap.restrictScalars ℝ
  let L := b⁻¹ • T
  refine ⟨L.continuous.comp_stronglyMeasurable hd, ?_, ?_, ?_⟩
  · exact Filter.Eventually.of_forall fun x =>
      (hg.2.1 x).smul (show IsSelfAdjoint b⁻¹ from rfl)
  · apply Filter.Eventually.of_forall
    intro x
    change ‖b⁻¹ • matrixL2Equiv (d r x)‖ ≤ 1
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hb.le)]
    have hx : ‖matrixL2Equiv (d r x)‖ ≤ b :=
      (gaussianHermitianIncrement_operator_le μ hX v a ha t K R hR r x).trans hbnd
    exact (mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hb.le)).trans_eq
      (inv_mul_cancel₀ hb.ne')
  · have hz : (gaussianSequentialMatrixLaw μ v a t)[L ∘ d r | rowMajorFiltration N N r]
        =ᵐ[gaussianSequentialMatrixLaw μ v a t] 0 := by
      filter_upwards [L.comp_condExp_comm hg.1 (m := rowMajorFiltration N N r), hg.2.2]
        with x hx hz
      change (gaussianSequentialMatrixLaw μ v a t)[L ∘ d r | rowMajorFiltration N N r] x = 0
      rw [← hx]
      simp only [Function.comp_apply, hz, Pi.zero_apply, map_zero]
    exact hz

/-- Trace expectation for the constructed cumulative process on the unchanged coupling. -/
theorem gaussianHermitianState_trace_le [NeZero N]
    (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (v : ℕ → 𝕂) (a : ℝ) (ha : 0 < a)
    (t : Fin N → 𝕂) (K R : ℝ) (hR : 0 ≤ R) (b : ℝ) (hb : 0 < b)
    (hbnd : 2*R/Real.sqrt (N : ℝ) ≤ b) (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1/2)
    (n : ℕ) :
    let P := gaussianSequentialMatrixLaw μ v a t
    let X := gaussianHermitianUnitIncrement μ v a t K R b
    (∫ x, RCLike.re (NormedSpace.exp
      (matrixCompensatedState P (rowMajorFiltration N N) X s n x)).trace ∂P) ≤ 2*(N : ℝ) := by
  have : IsProbabilityMeasure (gaussianSequentialMatrixLaw μ v a t) :=
    gaussianSequentialMatrixLaw_probability μ v a ha t
  have hg := gaussianHermitianUnitIncrement_basics μ hX v a ha t K R hR b hb hbnd
  have ht := matrixCompensatedState_trace_le (rowMajorFiltration N N)
    (gaussianHermitianUnitIncrement μ v a t K R b)
    (fun r => (hg r).1) (fun r => (hg r).2.1)
    (fun r => (hg r).2.2.1) (fun r => (hg r).2.2.2) hs hs1 n
  simpa only [Fintype.card_sum, Fintype.card_fin, Nat.cast_add, two_mul] using ht

#print axioms gaussianHermitianUnitIncrement_basics
#print axioms gaussianHermitianState_trace_le
end SpectralRadiusUpperTail

import SpectralRadiusUpperTail.GaussianMatrixTruncationMoment
import SpectralRadiusUpperTail.MatrixOperatorComparison

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators Matrix.Norms.Frobenius
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂] {N : ℕ}

/-- A quantitative operator-norm tail for the actual stopped truncation error. -/
theorem gaussianMatrixTruncationError_operator_probability_le
    (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (hm : (∫ x : 𝕂, x ∂μ) = 0)
    (hvar : (∫ x : 𝕂, ‖x‖^2 ∂μ) = 1) (v : ℕ → 𝕂)
    (hv : ∑ j : Fin N, ‖v j.val‖^2 ≤ 1) (a d : ℝ) (ha : 0 < a) (hd : 0 < d)
    (hexp : Integrable (fun x : 𝕂 => Real.exp (4*d*‖x‖^2)) μ)
    (t : Fin N → 𝕂) (K δ R : ℝ) (hK : 0 ≤ K) (hδ : δ ≤ 1) (hR : 0 ≤ R)
    (hb : ∀ j : Fin N, ‖v j.val‖ ≤ δ)
    (hunit : gaussianTruncationScale μ a d K*δ ≤ 1)
    (herror : (gaussianTruncationScale μ a d K*δ)*gaussianLocalMomentCost μ d ≤ 1/2)
    (r : ℝ) (hr : 0 < r) :
    (gaussianSequentialMatrixLaw μ v a t).real
      {x | r ≤ ‖Matrix.toEuclideanCLM (n := Fin N) (𝕜 := 𝕂)
        (gaussianMatrixTruncationError μ v a t K R x)‖} ≤
      ((N : ℝ)*gaussianTruncationTail μ d R)/r^2 := by
  have : IsProbabilityMeasure (gaussianSequentialMatrixLaw μ v a t) :=
    gaussianSequentialMatrixLaw_probability μ v a ha t
  obtain ⟨hi, hbnd⟩ := gaussianMatrixTruncationError_secondMoment_le
    μ hX hm hvar v hv a d ha hd hexp t K δ R hK hδ hR hb hunit herror
  exact (operator_probability_le_frobenius _ _ r).trans
    ((norm_probability_le_secondMoment _ _ hi r hr).trans (div_le_div_of_nonneg_right hbnd (sq_nonneg r)))

/-- The same coupling compares the original centered matrix to its truncation.
The only extra exceptional event is the actual bad-prefix event. -/
theorem gaussianCenteredMatrix_truncation_probability_le
    (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (hm : (∫ x : 𝕂, x ∂μ) = 0)
    (hvar : (∫ x : 𝕂, ‖x‖^2 ∂μ) = 1) (v : ℕ → 𝕂)
    (hv : ∑ j : Fin N, ‖v j.val‖^2 ≤ 1) (a d : ℝ) (ha : 0 < a) (hd : 0 < d)
    (hexp : Integrable (fun x : 𝕂 => Real.exp (4*d*‖x‖^2)) μ)
    (t : Fin N → 𝕂) (K δ R : ℝ) (hK : 0 ≤ K) (hδ : δ ≤ 1) (hR : 0 ≤ R)
    (hb : ∀ j : Fin N, ‖v j.val‖ ≤ δ)
    (hunit : gaussianTruncationScale μ a d K*δ ≤ 1)
    (herror : (gaussianTruncationScale μ a d K*δ)*gaussianLocalMomentCost μ d ≤ 1/2)
    (r : ℝ) (hr : 0 < r) :
    (gaussianSequentialMatrixLaw μ v a t).real
      {x | r ≤ ‖Matrix.toEuclideanCLM (n := Fin N) (𝕜 := 𝕂)
        (gaussianCenteredMatrix μ a v t (fun i => coordinateVector Prod.fst N (x i))
          (fun i => comparatorVector N (x i))-gaussianTruncatedMatrix μ v a t K R x)‖} ≤
      (gaussianSequentialMatrixLaw μ v a t).real (gaussianMatrixSafeEvent v t K)ᶜ +
        ((N : ℝ)*gaussianTruncationTail μ d R)/r^2 := by
  have : IsProbabilityMeasure (gaussianSequentialMatrixLaw μ v a t) :=
    gaussianSequentialMatrixLaw_probability μ v a ha t
  have hsub : {x | r ≤ ‖Matrix.toEuclideanCLM (n := Fin N) (𝕜 := 𝕂)
        (gaussianCenteredMatrix μ a v t (fun i => coordinateVector Prod.fst N (x i))
          (fun i => comparatorVector N (x i))-gaussianTruncatedMatrix μ v a t K R x)‖} ⊆
      (gaussianMatrixSafeEvent v t K)ᶜ ∪
        {x | r ≤ ‖Matrix.toEuclideanCLM (n := Fin N) (𝕜 := 𝕂)
          (gaussianMatrixTruncationError μ v a t K R x)‖} := by
    intro x hx
    by_cases hs : x ∈ gaussianMatrixSafeEvent v t K
    · right
      change r ≤ ‖Matrix.toEuclideanCLM (n := Fin N) (𝕜 := 𝕂)
        (gaussianMatrixTruncationError μ v a t K R x)‖
      unfold gaussianMatrixTruncationError
      rw [gaussianStoppedMatrix_eq_on_safe μ v a t K x hs]
      exact hx
    · exact Or.inl hs
  exact (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans
    (add_le_add_right (gaussianMatrixTruncationError_operator_probability_le
      μ hX hm hvar v hv a d ha hd hexp t K δ R hK hδ hR hb hunit herror r hr) _))

#print axioms gaussianCenteredMatrix_truncation_probability_le
end SpectralRadiusUpperTail

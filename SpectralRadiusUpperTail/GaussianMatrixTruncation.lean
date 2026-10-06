import SpectralRadiusUpperTail.RowMajorConditional
import SpectralRadiusUpperTail.GaussianStoppedTruncationBasics
import SpectralRadiusUpperTail.GaussianStoppedConditionalVariance
import SpectralRadiusUpperTail.GaussianSequentialMatrix

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped MeasureTheory BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂] {N : ℕ}

/-- The actual bounded stopped entry, regarded as a function on the fixed
coupled matrix space. Its column is N-(n+1), in the original coordinates. -/
noncomputable def gaussianMatrixTruncatedEntry (μ : Measure 𝕂) [SFinite μ]
    (v : ℕ → 𝕂) (a : ℝ) (t : Fin N → 𝕂) (K R : ℝ) (i : Fin N) (n : ℕ) :
    (Fin N → Fin N → 𝕂 × 𝕂) → 𝕂 :=
  fun x => gaussianTruncatedStoppedIncrement μ v a N (t i) K R n (x i)

/-- Conditional centering and adaptation hold against the entire matrix
past, including every completed row, under the same fixed matrix coupling. -/
theorem gaussianMatrixTruncatedEntry_basics (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (v : ℕ → 𝕂) (a : ℝ) (ha : 0 < a)
    (t : Fin N → 𝕂) (K R : ℝ) (hR : 0 ≤ R) (i : Fin N) (n : ℕ) :
    Integrable (gaussianMatrixTruncatedEntry μ v a t K R i n) (gaussianSequentialMatrixLaw μ v a t) ∧
      (gaussianSequentialMatrixLaw μ v a t)[gaussianMatrixTruncatedEntry μ v a t K R i n |
        rowMajorFiltration N N (i.val*N+n)] =ᵐ[gaussianSequentialMatrixLaw μ v a t] 0 ∧
      Measurable[rowMajorFiltration N N (i.val*N+n+1)] (gaussianMatrixTruncatedEntry μ v a t K R i n) ∧
      Integrable (fun x => ‖gaussianMatrixTruncatedEntry μ v a t K R i n x‖^2)
        (gaussianSequentialMatrixLaw μ v a t) := by
  have (j : Fin N) : IsProbabilityMeasure (gaussianSequentialRowLaw μ v a N (t j) N) :=
    gaussianSequentialRowLaw_probability μ v a ha N (t j) N
  let P := fun j : Fin N => gaussianSequentialRowLaw μ v a N (t j) N
  have hb := gaussianTruncatedStoppedIncrement_basics μ hX v a ha N (t i) K R hR n
  refine ⟨(measurePreserving_eval P i).integrable_comp_of_integrable hb.1,
    condExp_pi_rowMajor_zero P i n _ hb.1 hb.2.1, ?_,
    (measurePreserving_eval P i).integrable_comp_of_integrable hb.2.2.2⟩
  have hd := hb.2.2.1.comp (rowMajorFiltration_current N N (n+1) i)
  rw [← Nat.add_assoc] at hd
  exact hd

lemma gaussianMatrixTruncatedEntry_norm_le (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (v : ℕ → 𝕂) (a : ℝ) (ha : 0 < a)
    (t : Fin N → 𝕂) (K R : ℝ) (hR : 0 ≤ R) (i : Fin N) (n : ℕ)
    (x : Fin N → Fin N → 𝕂 × 𝕂) :
    ‖gaussianMatrixTruncatedEntry μ v a t K R i n x‖ ≤ 2*R :=
  gaussianTruncatedStoppedIncrement_norm_le μ hX v a ha N (t i) K R hR n (x i)

/-- The coefficient-dependent conditional variance bound holds relative to
the full row-major matrix filtration, not merely a single-row history. -/
theorem gaussianMatrixTruncatedEntry_conditional_variance_le
    (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (hm : (∫ x : 𝕂, x ∂μ) = 0)
    (hvar : (∫ x : 𝕂, ‖x‖^2 ∂μ) = 1) (v : ℕ → 𝕂)
    (hv : ∑ j : Fin N, ‖v j.val‖^2 ≤ 1) (a d : ℝ) (ha : 0 < a) (hd : 0 < d)
    (hexp : Integrable (fun x : 𝕂 => Real.exp (4*d*‖x‖^2)) μ)
    (t : Fin N → 𝕂) (i : Fin N) (n : ℕ) (hn : n < N)
    (K δ R : ℝ) (hK : 0 ≤ K) (hδ : δ ≤ 1) (hR : 0 ≤ R)
    (hb : ‖v (N-(n+1))‖ ≤ δ)
    (hunit : gaussianTruncationScale μ a d K*δ ≤ 1)
    (herror : (gaussianTruncationScale μ a d K*δ)*gaussianLocalMomentCost μ d ≤ 1/2) :
    ∀ᵐ x ∂gaussianSequentialMatrixLaw μ v a t,
      (gaussianSequentialMatrixLaw μ v a t)[
        (fun y => ‖gaussianMatrixTruncatedEntry μ v a t K R i n y‖^2) |
        rowMajorFiltration N N (i.val*N+n)] x ≤
          (12*gaussianTruncationScale μ a d K*gaussianLocalMomentCost μ d)*‖v (N-(n+1))‖ := by
  have (j : Fin N) : IsProbabilityMeasure (gaussianSequentialRowLaw μ v a N (t j) N) :=
    gaussianSequentialRowLaw_probability μ v a ha N (t j) N
  have hi := (gaussianTruncatedStoppedIncrement_basics μ hX v a ha N (t i) K R hR n).2.2.2
  exact condExp_pi_rowMajor_le (fun j : Fin N => gaussianSequentialRowLaw μ v a N (t j) N)
    i n _ hi _ (gaussianTruncatedStoppedIncrement_conditional_variance_le
      μ hX hm hvar v N hv a d ha hd hexp (t i) n hn K δ R hK hδ hR hb hunit herror)

#print axioms gaussianMatrixTruncatedEntry_basics
#print axioms gaussianMatrixTruncatedEntry_conditional_variance_le
end SpectralRadiusUpperTail

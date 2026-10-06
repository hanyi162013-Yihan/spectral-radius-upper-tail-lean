import SpectralRadiusUpperTail.GaussianStoppingProbability
import SpectralRadiusUpperTail.GaussianSequentialMatrix
import SpectralRadiusUpperTail.ActualMatrixIdentity

namespace SpectralRadiusUpperTail
open MeasureTheory Matrix
open scoped BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂] {N : ℕ}

lemma gaussianSequentialMatrixLaw_row (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (v : ℕ → 𝕂) (a : ℝ) (ha : 0 < a) (t : Fin N → 𝕂) (i : Fin N) :
    (gaussianSequentialMatrixLaw μ v a t).map (fun x => x i) =
      gaussianSequentialRowLaw μ v a N (t i) N := by
  have (k : Fin N) : IsProbabilityMeasure (gaussianSequentialRowLaw μ v a N (t k) N) :=
    gaussianSequentialRowLaw_probability μ v a ha N (t k) N
  exact (measurePreserving_eval _ i).map_eq

def gaussianMatrixSafeEvent (v : ℕ → 𝕂) (t : Fin N → 𝕂) (R : ℝ) :
    Set (Fin N → Fin N → 𝕂 × 𝕂) :=
  {x | ∀ i, x i ∈ prefixSafeEvent (gaussianTerminalTarget v N (t i)) R N}

lemma gaussianRowSafeEvent_measurable (v : ℕ → 𝕂) (N : ℕ) (t : 𝕂) (R : ℝ) :
    MeasurableSet (prefixSafeEvent (gaussianTerminalTarget v N t) R N) := by
  have hh := prefixSafeEvent_measurable (pathFiltration N) _
    (gaussianTerminalTarget_measurable v N t) R N
  rw [pathFiltration_of_ge N N le_rfl] at hh
  exact hh

lemma gaussianMatrixSafeEvent_measurable (v : ℕ → 𝕂) (t : Fin N → 𝕂) (R : ℝ) :
    MeasurableSet (gaussianMatrixSafeEvent v t R) := by
  unfold gaussianMatrixSafeEvent
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter (fun i =>
    (gaussianRowSafeEvent_measurable v N (t i) R).preimage (measurable_pi_apply i))

/-- Actual whole-array stopping probability, using exact row marginals. -/
theorem gaussianMatrix_bad_prefix_probability (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hm : (∫ x : 𝕂, x ∂μ) = 0) (hvar : (∫ x : 𝕂, ‖x‖^2 ∂μ) = 1)
    (τ : ℝ) (hτ : 0 < τ) (hexp : Integrable (fun x : 𝕂 => Real.exp (τ*‖x‖^2)) μ)
    (v : ℕ → 𝕂) (hv : ∑ i : Fin N, ‖v i.val‖^2 ≤ 1)
    (a : ℝ) (ha : 0 < a) (t : Fin N → 𝕂) (K : ℝ) (ht : ∀ i, ‖t i‖ ≤ K)
    (R : ℝ) (hR : 0 ≤ R) :
    let c := rowSquareExpExponent τ (∫ x : 𝕂, Real.exp (τ*‖x‖^2) ∂μ)
    (gaussianSequentialMatrixLaw μ v a t).real (gaussianMatrixSafeEvent v t R)ᶜ ≤
      (N : ℝ)*((N+1 : ℕ)*((2*Real.exp ((K^2+1)/a+c*K^2))*Real.exp (-(c/2)*R^2))) := by
  have (i : Fin N) : IsProbabilityMeasure (gaussianSequentialRowLaw μ v a N (t i) N) :=
    gaussianSequentialRowLaw_probability μ v a ha N (t i) N
  have : IsProbabilityMeasure (gaussianSequentialMatrixLaw μ v a t) :=
    gaussianSequentialMatrixLaw_probability μ v a ha t
  have he : (gaussianMatrixSafeEvent v t R)ᶜ =
      ⋃ i : Fin N, {x | x i ∉ prefixSafeEvent (gaussianTerminalTarget v N (t i)) R N} := by
    ext x
    simp [gaussianMatrixSafeEvent, not_forall]
  rw [he]
  apply (measureReal_iUnion_fintype_le _).trans
  calc
    _ ≤ ∑ i : Fin N, (N+1 : ℕ)*((2*Real.exp ((K^2+1)/a+
        rowSquareExpExponent τ (∫ x : 𝕂, Real.exp (τ*‖x‖^2) ∂μ)*K^2))*
        Real.exp (-(rowSquareExpExponent τ (∫ x : 𝕂, Real.exp (τ*‖x‖^2) ∂μ)/2)*R^2)) := by
      apply Finset.sum_le_sum
      intro i _
      have hi := gaussianStoppedRow_bad_probability μ hm hvar τ hτ hexp v N hv a ha (t i) K (ht i) R hR
      have hmarg := gaussianSequentialMatrixLaw_row μ v a ha t i
      have hp : (gaussianSequentialMatrixLaw μ v a t).real
          {x | x i ∉ prefixSafeEvent (gaussianTerminalTarget v N (t i)) R N} =
          (gaussianSequentialRowLaw μ v a N (t i) N).real
            (prefixSafeEvent (gaussianTerminalTarget v N (t i)) R N)ᶜ := by
        rw [← hmarg]
        change ((gaussianSequentialMatrixLaw μ v a t) _).toReal =
          (((gaussianSequentialMatrixLaw μ v a t).map (fun x => x i)) _).toReal
        rw [Measure.map_apply (measurable_pi_apply i) (gaussianRowSafeEvent_measurable v N (t i) R).compl]
        rfl
      rw [hp]
      exact hi
    _ = _ := by simp

noncomputable def gaussianStoppedMatrix (μ : Measure 𝕂) (v : ℕ → 𝕂) (a : ℝ)
    (t : Fin N → 𝕂) (R : ℝ) (x : Fin N → Fin N → 𝕂 × 𝕂) : Matrix (Fin N) (Fin N) 𝕂 :=
  fun i j => (1/Real.sqrt (N : ℝ) : ℝ) •
    gaussianStoppedIncrement μ v a N (t i) R (N-(j.val+1)) (x i)

/-- If no actual prefix is bad, stopping preserves the entire centered error matrix. -/
theorem gaussianStoppedMatrix_eq_on_safe (μ : Measure 𝕂) (v : ℕ → 𝕂) (a : ℝ)
    (t : Fin N → 𝕂) (R : ℝ) (x : Fin N → Fin N → 𝕂 × 𝕂)
    (hx : x ∈ gaussianMatrixSafeEvent v t R) :
    gaussianStoppedMatrix μ v a t R x = gaussianCenteredMatrix μ a v t
      (fun i => coordinateVector Prod.fst N (x i)) (fun i => comparatorVector N (x i)) := by
  ext i j
  have hs := prefixSafeEvent_antitone (gaussianTerminalTarget v N (t i)) R
    (show N-(j.val+1) ≤ N from Nat.sub_le _ _) (hx i)
  change (1/Real.sqrt (N : ℝ) : ℝ) •
    (prefixSafeEvent (gaussianTerminalTarget v N (t i)) R (N-(j.val+1))).indicator
      (gaussianTerminalIncrement μ v a N (t i) (N-(j.val+1))) (x i) = _
  rw [Set.indicator_of_mem hs, gaussianTerminalIncrement_at_coordinate]
  rfl

#print axioms gaussianMatrix_bad_prefix_probability
#print axioms gaussianStoppedMatrix_eq_on_safe
end SpectralRadiusUpperTail

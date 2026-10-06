import SpectralRadiusUpperTail.PairedAssignmentMoment

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
variable {k n : ℕ}

/-- A finite sum of pattern moments, independent of the matrix dimension. -/
noncomputable def pairedMomentConstant (μ : Measure 𝕂) (k : ℕ) : ℝ := by
  classical
  exact ∑ r : Setoid (Fin (k+1) ⊕ Fin (k+1)), ‖pairedPatternMoment μ r‖

lemma pairedMomentConstant_nonneg (μ : Measure 𝕂) (k : ℕ) : 0 ≤ pairedMomentConstant μ k := by
  classical
  unfold pairedMomentConstant
  exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)

lemma pairedAssignment_weighted_relabel (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (r : Setoid (Fin (k+1) ⊕ Fin (k+1))) [DecidableRel r.r]
    (p q : Fin n → 𝕂) (f : Quotient r → Fin n) (hf : Function.Injective f) :
    pairedAssignmentWeight p q (fun a => f (Quotient.mk r a)) *
      ‖pairedAssignmentMoment μ (fun a => f (Quotient.mk r a))‖ =
    ‖pairedPatternMoment μ r‖ * pairedPatternEndpointWeight r p q f := by
  have hm := congrArg norm (pairedAssignmentMoment_relabel μ r f hf)
  have hw := pairedAssignmentWeight_relabel r p q f
  exact (congrArg₂ (fun a b : ℝ => a*b) hw hm).trans (mul_comm _ _)

/-- Only injective label assignments are used when extracting the fixed
pattern moment; no relabeling claim is made for noninjective assignments. -/
lemma pairedAssignment_pattern_factor (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (r : Setoid (Fin (k+1) ⊕ Fin (k+1))) [DecidableRel r.r] (p q : Fin n → 𝕂) :
    equalityPatternContribution r
      (fun x => pairedAssignmentWeight p q x * ‖pairedAssignmentMoment μ x‖) =
    ‖pairedPatternMoment μ r‖ *
      ∑ f : {f : Quotient r → Fin n // Function.Injective f},
        pairedPatternEndpointWeight r p q f.1 := by
  classical
  unfold equalityPatternContribution
  calc
    _ = ∑ f : {f : Quotient r → Fin n // Function.Injective f},
        ‖pairedPatternMoment μ r‖ * pairedPatternEndpointWeight r p q f.1 := by
      refine Finset.sum_congr ?_ ?_
      · ext f
        simp only [Finset.mem_univ]
      · intro f _
        exact pairedAssignment_weighted_relabel μ r p q f.1 f.2
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- Actual finite sum of absolute paired-edge moment contributions, with
all deterministic endpoint weights, bounded uniformly in dimension. -/
lemma pairedAssignment_total_bound (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hm : (∫ x : 𝕂, x ∂μ) = 0) (hk : 0 < k) (hn : 0 < n)
    (p q : Fin n → 𝕂) (hp : (∑ i, ‖p i‖^2) ≤ 1) (hq : (∑ i, ‖q i‖^2) ≤ 1) :
    (∑ x : (Fin (k+1) ⊕ Fin (k+1)) → Fin n,
      pairedAssignmentWeight p q x * ‖pairedAssignmentMoment μ x‖) ≤
      pairedMomentConstant μ k * (n : ℝ)^(k-1) := by
  classical
  rw [sum_eq_equalityPatterns]
  calc
    _ ≤ ∑ r : Setoid (Fin (k+1) ⊕ Fin (k+1)),
        ‖pairedPatternMoment μ r‖ * (n : ℝ)^(k-1) := by
      apply Finset.sum_le_sum
      intro r _
      rw [pairedAssignment_pattern_factor]
      exact pairedPattern_weighted_sum_le μ hm hk hn r p q hp hq
    _ = _ := by
      unfold pairedMomentConstant
      rw [Finset.sum_mul]

#print axioms pairedMomentConstant
#print axioms pairedMomentConstant_nonneg
#print axioms pairedAssignment_weighted_relabel
#print axioms pairedAssignment_pattern_factor
#print axioms pairedAssignment_total_bound
end SpectralRadiusUpperTail

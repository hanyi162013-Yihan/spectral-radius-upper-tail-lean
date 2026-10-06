import SpectralRadiusUpperTail.PairedPatternEndpoints
import SpectralRadiusUpperTail.EndpointAssignmentBound
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
variable {k n : ℕ}

noncomputable def pairedPatternEndpointWeight
    (r : Setoid (Fin (k+1) ⊕ Fin (k+1))) (p q : Fin n → 𝕂)
    (f : Quotient r → Fin n) : ℝ :=
  ‖p (f (patternLeftVertex r 0))‖ * ‖q (f (patternLeftVertex r (Fin.last k)))‖ *
    ‖p (f (patternRightVertex r 0))‖ * ‖q (f (patternRightVertex r (Fin.last k)))‖

lemma pairedPatternEndpointWeight_nonneg
    (r : Setoid (Fin (k+1) ⊕ Fin (k+1))) (p q : Fin n → 𝕂) (f : Quotient r → Fin n) :
    0 ≤ pairedPatternEndpointWeight r p q f := by
  unfold pairedPatternEndpointWeight
  positivity

/-- Every nonzero pattern has the same n^(k-1) endpoint-sum bound. -/
lemma pairedPattern_endpoint_sum_le (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hm : (∫ x : 𝕂, x ∂μ) = 0) (hk : 0 < k) (hn : 0 < n)
    (r : Setoid (Fin (k+1) ⊕ Fin (k+1))) [DecidableRel r.r]
    (p q : Fin n → 𝕂) (hp : (∑ i, ‖p i‖^2) ≤ 1) (hq : (∑ i, ‖q i‖^2) ≤ 1)
    (hr : pairedPatternMoment μ r ≠ 0) :
    (∑ f : Quotient r → Fin n, pairedPatternEndpointWeight r p q f) ≤ (n : ℝ)^(k-1) := by
  rcases pairedPattern_nonzero_structure μ hm hk r hr with hsmall | hs
  · calc
      _ ≤ (n : ℝ)^(Fintype.card (Quotient r)-1) := by
        simpa only [pairedPatternEndpointWeight, Fintype.card_fin] using
          endpoint_assignment_sum_le p q hp hq (patternLeftVertex r 0)
            (patternLeftVertex r (Fin.last k)) (patternRightVertex r 0)
            (patternRightVertex r (Fin.last k))
      _ ≤ _ := by
        apply pow_le_pow_right₀
        · exact_mod_cast (Nat.succ_le_of_lt hn)
        · omega
  · obtain ⟨he,hcard,hend⟩ := pairedPattern_simple_endpoints hk r hs.1 hs.2.1 hs.2.2
    have hb := endpoint_assignment_simple_path_le p q hp hq
      (patternLeftVertex r 0) (patternLeftVertex r (Fin.last k)) hend
    have hexp : k+1-2 = k-1 := by omega
    simpa only [pairedPatternEndpointWeight, ← he, hcard, Fintype.card_fin, hexp] using hb

lemma pairedPattern_injective_endpoint_sum_le (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hm : (∫ x : 𝕂, x ∂μ) = 0) (hk : 0 < k) (hn : 0 < n)
    (r : Setoid (Fin (k+1) ⊕ Fin (k+1))) [DecidableRel r.r]
    (p q : Fin n → 𝕂) (hp : (∑ i, ‖p i‖^2) ≤ 1) (hq : (∑ i, ‖q i‖^2) ≤ 1)
    (hr : pairedPatternMoment μ r ≠ 0) :
    (∑ f : {f : Quotient r → Fin n // Function.Injective f},
      pairedPatternEndpointWeight r p q f.1) ≤ (n : ℝ)^(k-1) := by
  classical
  calc
    _ ≤ ∑ f : Quotient r → Fin n, pairedPatternEndpointWeight r p q f := by
      rw [← Finset.sum_subtype
        (Finset.univ.filter (fun f : Quotient r → Fin n => Function.Injective f))
        (by intro f; simp) (pairedPatternEndpointWeight r p q)]
      exact Finset.sum_le_univ_sum_of_nonneg (pairedPatternEndpointWeight_nonneg r p q)
    _ ≤ _ := pairedPattern_endpoint_sum_le μ hm hk hn r p q hp hq hr

/-- Pattern moment times its actual injective endpoint sum, including zero moments. -/
lemma pairedPattern_weighted_sum_le (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hm : (∫ x : 𝕂, x ∂μ) = 0) (hk : 0 < k) (hn : 0 < n)
    (r : Setoid (Fin (k+1) ⊕ Fin (k+1))) [DecidableRel r.r]
    (p q : Fin n → 𝕂) (hp : (∑ i, ‖p i‖^2) ≤ 1) (hq : (∑ i, ‖q i‖^2) ≤ 1) :
    ‖pairedPatternMoment μ r‖ *
      (∑ f : {f : Quotient r → Fin n // Function.Injective f},
        pairedPatternEndpointWeight r p q f.1) ≤
      ‖pairedPatternMoment μ r‖ * (n : ℝ)^(k-1) := by
  by_cases hr : pairedPatternMoment μ r = 0
  · simp [hr]
  · exact mul_le_mul_of_nonneg_left
      (pairedPattern_injective_endpoint_sum_le μ hm hk hn r p q hp hq hr) (norm_nonneg _)

#print axioms pairedPatternEndpointWeight
#print axioms pairedPatternEndpointWeight_nonneg
#print axioms pairedPattern_endpoint_sum_le
#print axioms pairedPattern_injective_endpoint_sum_le
#print axioms pairedPattern_weighted_sum_le
end SpectralRadiusUpperTail

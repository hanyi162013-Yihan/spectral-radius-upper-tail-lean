import SpectralRadiusUpperTail.TalagrandCompactIidStep
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory WithLp Set
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]

/-- Talagrand's exponential convex-distance inequality for every compact
target under an arbitrary finite iid product law. -/
theorem talagrand_compact_moment_induction
    (μ : Measure 𝕂) [IsProbabilityMeasure μ] :
    ∀ N : ℕ, ∀ A : Set (EuclideanSpace 𝕂 (Fin N)), IsCompact A →
      (talagrandEuclideanProductLaw μ N).real A *
        (∫ x, Real.exp (mismatchHullEnergy x A/4)
          ∂talagrandEuclideanProductLaw μ N) ≤ 1 := by
  intro N
  induction N with
  | zero =>
      intro A hA
      have henergy (x : EuclideanSpace 𝕂 (Fin 0)) :
          mismatchHullEnergy x A = 0 := by
        have h := mismatchHullEnergy_bounds x A
        norm_num at h ⊢
        linarith
      have hI : (∫ x, Real.exp (mismatchHullEnergy x A/4)
          ∂talagrandEuclideanProductLaw μ 0) = 1 := by
        simp [henergy]
      rw [hI, mul_one]
      calc
        (talagrandEuclideanProductLaw μ 0).real A ≤
            (talagrandEuclideanProductLaw μ 0).real Set.univ :=
          measureReal_mono (Set.subset_univ _)
        _ = 1 := by simp
  | succ N ih =>
      intro A hA
      let ν := talagrandEuclideanProductLaw μ N
      let B := euclideanCoordinateTail N '' A
      by_cases hpA : 0 < (talagrandEuclideanProductLaw μ (N+1)).real A
      · have hAne : A.Nonempty := by
          by_contra h
          have hnil : A = ∅ := Set.not_nonempty_iff_eq_empty.mp h
          simp only [hnil, measureReal_empty] at hpA
          exact (lt_irrefl 0) hpA
        have hBc : IsCompact B := projectedTarget_compact N A hA
        have hBm (hpB : 0 < ν.real B) :
            (∫ y, Real.exp (mismatchHullEnergy y B/4) ∂ν) ≤
              1/ν.real B := by
          apply (le_div_iff₀ hpB).2
          calc
            (∫ y, Real.exp (mismatchHullEnergy y B/4) ∂ν) * ν.real B =
                ν.real B * (∫ y, Real.exp (mismatchHullEnergy y B/4) ∂ν) :=
              mul_comm _ _
            _ ≤ 1 := ih B hBc
        have hFm (s : 𝕂) (hpos : 0 < ν.real
            {y : EuclideanSpace 𝕂 (Fin N) | euclideanWithHead N s y ∈ A}) :
            (∫ y, Real.exp (mismatchHullEnergy y
              {z : EuclideanSpace 𝕂 (Fin N) |
                euclideanWithHead N s z ∈ A}/4) ∂ν) ≤
            1/ν.real {y : EuclideanSpace 𝕂 (Fin N) |
              euclideanWithHead N s y ∈ A} := by
          let F : Set (EuclideanSpace 𝕂 (Fin N)) :=
            {y | euclideanWithHead N s y ∈ A}
          let x : EuclideanSpace 𝕂 (Fin (N+1)) := euclideanWithHead N s 0
          have hFc : IsCompact F := by
            simpa [F, x, matchingHeadFiber, euclideanWithHead] using
              matchingHeadFiber_compact N x A hA
          apply (le_div_iff₀ hpos).2
          change (∫ y, Real.exp (mismatchHullEnergy y F/4) ∂ν) * ν.real F ≤ 1
          calc
            (∫ y, Real.exp (mismatchHullEnergy y F/4) ∂ν) * ν.real F =
                ν.real F * (∫ y, Real.exp (mismatchHullEnergy y F/4) ∂ν) :=
              mul_comm _ _
            _ ≤ 1 := ih F hFc
        exact talagrand_compact_iid_step μ N A hA hAne hpA hBm hFm
      · have hpAz : (talagrandEuclideanProductLaw μ (N+1)).real A = 0 :=
          le_antisymm (le_of_not_gt hpA) measureReal_nonneg
        rw [hpAz, zero_mul]
        norm_num

#print axioms talagrand_compact_moment_induction
end SpectralRadiusUpperTail

import SpectralRadiusUpperTail.TalagrandCompactMomentInduction
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory WithLp Set
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]

/-- The exponential moment bound implies convex-hull separation when the
first target is compact. -/
theorem talagrand_compact_separation
    (μ : Measure 𝕂) [IsProbabilityMeasure μ] (N : ℕ)
    (S T : Set (EuclideanSpace 𝕂 (Fin N)))
    (hS : IsCompact S) (hT : IsClosed T)
    (t : ℝ) (ht : 0 ≤ t)
    (hsep : ∀ x ∈ T, ∀ v ∈ mismatchHull x S, t ≤ ‖v‖) :
    (talagrandEuclideanProductLaw μ N).real S *
      (talagrandEuclideanProductLaw μ N).real T ≤
      Real.exp (-(1/4)*t^2) := by
  let ν := talagrandEuclideanProductLaw μ N
  by_cases hSne : S.Nonempty
  · let e := fun x : EuclideanSpace 𝕂 (Fin N) =>
      mismatchHullEnergy x S/4
    let f := fun x : EuclideanSpace 𝕂 (Fin N) => Real.exp (e x)
    let ε := Real.exp (t^2/4)
    have he : Measurable e :=
      (mismatchHullEnergy_measurable S hS).div_const 4
    have hb (x : EuclideanSpace 𝕂 (Fin N)) : e x ≤ (N : ℝ)/4 := by
      exact (div_le_div_of_nonneg_right
        (mismatchHullEnergy_bounds x S).2 (by norm_num))
    have hfi : Integrable f ν :=
      integrable_exp_of_bounded_energy ν e he _ hb
    have hε : 0 < ε := Real.exp_pos _
    have hsub : T ⊆ {x | ε ≤ f x} := by
      intro x hx
      obtain ⟨v, hv, heq, _⟩ := mismatchHullEnergy_minimum x S hSne
      have hnorm := hsep x hx v hv
      have henergy : t^2 ≤ mismatchHullEnergy x S := by
        rw [heq]
        nlinarith [norm_nonneg v]
      exact Real.exp_le_exp.mpr (by dsimp [e, ε]; linarith)
    have hmark : ε*ν.real T ≤ ∫ x, f x ∂ν := by
      have hM := mul_meas_ge_le_integral_of_nonneg
        (μ := ν) (f := f)
        (Filter.Eventually.of_forall (fun x => (Real.exp_pos (e x)).le))
        hfi ε
      calc
        ε*ν.real T ≤ ε*ν.real {x | ε ≤ f x} :=
          mul_le_mul_of_nonneg_left
            (measureReal_mono hsub (measure_ne_top ν _)) hε.le
        _ ≤ ∫ x, f x ∂ν := hM
    have hMoment := talagrand_compact_moment_induction μ N S hS
    have hP : 0 ≤ ν.real S := measureReal_nonneg
    have hmix : ε*(ν.real S*ν.real T) ≤ 1 := by
      calc
        ε*(ν.real S*ν.real T) = ν.real S*(ε*ν.real T) := by ring
        _ ≤ ν.real S*(∫ x, f x ∂ν) :=
          mul_le_mul_of_nonneg_left hmark hP
        _ ≤ 1 := hMoment
    have hrhs : Real.exp (-(1/4)*t^2) = 1/ε := by
      dsimp [ε]
      rw [show -(1/4)*t^2 = -(t^2/4) by ring, Real.exp_neg]
      ring
    rw [hrhs]
    exact (le_div_iff₀ hε).2 (by simpa only [mul_comm] using hmix)
  · have hnil : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hSne
    rw [hnil, measureReal_empty, zero_mul]
    exact (Real.exp_pos _).le

#print axioms talagrand_compact_separation
end SpectralRadiusUpperTail

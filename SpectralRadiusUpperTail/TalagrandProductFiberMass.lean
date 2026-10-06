import SpectralRadiusUpperTail.TalagrandFiberMass
import SpectralRadiusUpperTail.FiniteSequentialLaw
import SpectralRadiusUpperTail.MismatchHullFiberInterpolation
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory WithLp
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂]

omit [RCLike 𝕂] in
lemma talagrand_measurable_head_cons (N : ℕ) :
    Measurable (fun z : 𝕂 × (Fin N → 𝕂) =>
      (Fin.cons z.1 z.2 : Fin (N+1) → 𝕂)) := by
  exact (measurable_fin_cons N).comp measurable_swap

lemma talagrand_iid_head_cons_map (μ : Measure 𝕂) [IsProbabilityMeasure μ] (N : ℕ) :
    (μ.prod (Measure.pi fun _ : Fin N => μ)).map
      (fun z : 𝕂 × (Fin N → 𝕂) => Fin.cons z.1 z.2) =
    Measure.pi (fun _ : Fin (N+1) => μ) := by
  simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_zero,
    Fin.consEquiv, Equiv.coe_fn_mk] using
    (measurePreserving_piFinSuccAbove (fun _ : Fin (N+1) => μ) 0).symm.map_eq

/-- The probability of a product-array event is the average of the
matching-head fiber probabilities. This connects the generic section
identity to the Euclidean coordinates used by the convex distance. -/
theorem talagrand_product_fiber_mass
    (μ : Measure 𝕂) [IsProbabilityMeasure μ] (N : ℕ)
    (A : Set (EuclideanSpace 𝕂 (Fin (N+1)))) (hA : MeasurableSet A) :
    (Measure.pi (fun _ : Fin (N+1) => μ)).real
      {z : Fin (N+1) → 𝕂 | (toLp 2 z : EuclideanSpace 𝕂 (Fin (N+1))) ∈ A} =
    ∫ s, (Measure.pi (fun _ : Fin N => μ)).real
      {z : Fin N → 𝕂 |
        euclideanWithHead N s (toLp 2 z : EuclideanSpace 𝕂 (Fin N)) ∈ A} ∂μ := by
  let P := Measure.pi (fun _ : Fin N => μ)
  let E : Set (Fin (N+1) → 𝕂) :=
    {z | (toLp 2 z : EuclideanSpace 𝕂 (Fin (N+1))) ∈ A}
  let S : Set (𝕂 × (Fin N → 𝕂)) :=
    {z | (toLp 2 (Fin.cons z.1 z.2) : EuclideanSpace 𝕂 (Fin (N+1))) ∈ A}
  have hE : MeasurableSet E := hA.preimage (WithLp.measurable_toLp 2 _)
  have hS : MeasurableSet S := hE.preimage (talagrand_measurable_head_cons N)
  have hmean :=
    (talagrand_fiber_mass_measurable_and_mean μ P S hS).2.2
  change (Measure.pi (fun _ : Fin (N+1) => μ)).real E =
    ∫ s, P.real {z : Fin N → 𝕂 |
      euclideanWithHead N s (toLp 2 z : EuclideanSpace 𝕂 (Fin N)) ∈ A} ∂μ
  calc
    (Measure.pi (fun _ : Fin (N+1) => μ)).real E =
        ((μ.prod P).map (fun z : 𝕂 × (Fin N → 𝕂) => Fin.cons z.1 z.2)).real E := by
          rw [talagrand_iid_head_cons_map]
    _ = (μ.prod P).real S := by
      simpa only [S, E, Set.preimage_ofPred_eq] using
        (map_measureReal_apply (talagrand_measurable_head_cons N) hE)
    _ = ∫ s, P.real {z : Fin N → 𝕂 |
        euclideanWithHead N s (toLp 2 z : EuclideanSpace 𝕂 (Fin N)) ∈ A} ∂μ := by
      simpa only [S, euclideanWithHead, Set.preimage_ofPred_eq] using hmean.symm

#print axioms talagrand_product_fiber_mass
end SpectralRadiusUpperTail

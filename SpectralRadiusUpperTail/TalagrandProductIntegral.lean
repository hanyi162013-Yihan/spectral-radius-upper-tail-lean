import SpectralRadiusUpperTail.TalagrandProductFiberMass
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory WithLp
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂]

/-- Fubini in the head/tail coordinates of a finite iid array, expressed
in the Euclidean coordinates used for convex mismatch distance. -/
theorem talagrand_product_integral_fubini
    (μ : Measure 𝕂) [IsProbabilityMeasure μ] (N : ℕ)
    (f : EuclideanSpace 𝕂 (Fin (N+1)) → ℝ) (hf : Measurable f)
    (hfi : Integrable
      (fun z : 𝕂 × (Fin N → 𝕂) =>
        f (toLp 2 (Fin.cons z.1 z.2)))
      (μ.prod (Measure.pi fun _ : Fin N => μ))) :
    (∫ z : Fin (N+1) → 𝕂,
      f (toLp 2 z : EuclideanSpace 𝕂 (Fin (N+1)))
        ∂Measure.pi (fun _ : Fin (N+1) => μ)) =
    ∫ s, ∫ z : Fin N → 𝕂,
      f (euclideanWithHead N s
        (toLp 2 z : EuclideanSpace 𝕂 (Fin N)))
        ∂Measure.pi (fun _ : Fin N => μ) ∂μ := by
  let P := Measure.pi (fun _ : Fin N => μ)
  let F := fun z : Fin (N+1) → 𝕂 =>
    f (toLp 2 z : EuclideanSpace 𝕂 (Fin (N+1)))
  have hF : StronglyMeasurable F :=
    (hf.comp (WithLp.measurable_toLp 2 _)).stronglyMeasurable
  have hmap : (μ.prod P).map
      (fun z : 𝕂 × (Fin N → 𝕂) => Fin.cons z.1 z.2) =
      Measure.pi (fun _ : Fin (N+1) => μ) :=
    talagrand_iid_head_cons_map μ N
  calc
    (∫ z : Fin (N+1) → 𝕂, F z
      ∂Measure.pi (fun _ : Fin (N+1) => μ)) =
        ∫ z : 𝕂 × (Fin N → 𝕂),
          F (Fin.cons z.1 z.2) ∂μ.prod P := by
      rw [← hmap]
      exact integral_map_of_stronglyMeasurable
        (talagrand_measurable_head_cons N) hF
    _ = ∫ s, ∫ z : Fin N → 𝕂,
          f (euclideanWithHead N s
            (toLp 2 z : EuclideanSpace 𝕂 (Fin N))) ∂P ∂μ := by
      convert integral_prod
        (fun z : 𝕂 × (Fin N → 𝕂) =>
          f (toLp 2 (Fin.cons z.1 z.2))) hfi using 1
      rfl

#print axioms talagrand_product_integral_fubini
end SpectralRadiusUpperTail

import SpectralRadiusUpperTail.TalagrandCompactSeparation
import SpectralRadiusUpperTail.TalagrandCoordinateBoxCompact
import SpectralRadiusUpperTail.CutoffTalagrandInput
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory WithLp Set
variable {𝕂 : Type*} [RCLike 𝕂]

/-- The bounded-cutoff convex-distance input follows from the proved iid
product moment inequality, for every real or complex entry law. -/
theorem cutoff_talagrand_hull_proved
    (μ : Measure 𝕂) [IsProbabilityMeasure μ] :
    CutoffTalagrandHull μ := by
  intro K N S T hS hT t ht hsep
  let κ := μ.map (entryCutoff (K : ℝ))
  letI : IsProbabilityMeasure κ :=
    Measure.isProbabilityMeasure_map
      (entryCutoff_measurable (K : ℝ)).aemeasurable
  let C := coordinateBox (𝕂 := 𝕂) N (K : ℝ)
  have hCc : IsCompact C := coordinateBox_compact N (K : ℝ)
  have hCclosed : IsClosed C := coordinateBox_closed N (K : ℝ)
  have hSc : IsCompact (S ∩ C) := hCc.inter_left hS
  have hTc : IsClosed (T ∩ C) := hT.inter hCclosed
  have hsep' : ∀ x ∈ T ∩ C, ∀ v ∈ mismatchHull x (S ∩ C),
      t ≤ ‖v‖ := by
    intro x hx v hv
    have hvS : v ∈ mismatchHull x S := by
      unfold mismatchHull at hv ⊢
      exact convexHull_mono (𝕜 := ℝ)
        (Set.image_mono (Set.inter_subset_left)) hv
    exact hsep x hx.1 v hvS
  have hcompact := talagrand_compact_separation κ N
    (S ∩ C) (T ∩ C) hSc hTc t ht hsep'
  have hsupport : ∀ᵐ x ∂Measure.pi (fun _ : Fin N => κ),
      (toLp 2 x : EuclideanSpace 𝕂 (Fin N)) ∈ C := by
    change ∀ᵐ x ∂Measure.pi (fun _ : Fin N => κ),
      ∀ i, ‖x i‖ ≤ (K : ℝ)
    apply ae_all_iff.mpr
    intro i
    exact (measurePreserving_eval (fun _ : Fin N => κ) i).quasiMeasurePreserving.ae
      (entryCutoff_law_supported μ (K : ℝ) (by positivity))
  have hSm : MeasurableSet S := hS.measurableSet
  have hTm : MeasurableSet T := hT.measurableSet
  have hSCm : MeasurableSet (S ∩ C) := hSm.inter hCclosed.measurableSet
  have hTCm : MeasurableSet (T ∩ C) := hTm.inter hCclosed.measurableSet
  have hEqS : (talagrandEuclideanProductLaw κ N).real (S ∩ C) =
      (talagrandEuclideanProductLaw κ N).real S := by
    rw [talagrandEuclideanProductLaw_real κ N (S ∩ C) hSCm,
      talagrandEuclideanProductLaw_real κ N S hSm]
    exact measureReal_preimage_inter_of_ae
      (Measure.pi (fun _ : Fin N => κ))
      (fun x : Fin N → 𝕂 => (toLp 2 x : EuclideanSpace 𝕂 (Fin N)))
      S C hsupport
  have hEqT : (talagrandEuclideanProductLaw κ N).real (T ∩ C) =
      (talagrandEuclideanProductLaw κ N).real T := by
    rw [talagrandEuclideanProductLaw_real κ N (T ∩ C) hTCm,
      talagrandEuclideanProductLaw_real κ N T hTm]
    exact measureReal_preimage_inter_of_ae
      (Measure.pi (fun _ : Fin N => κ))
      (fun x : Fin N → 𝕂 => (toLp 2 x : EuclideanSpace 𝕂 (Fin N)))
      T C hsupport
  change (Measure.pi (fun _ : Fin N => κ)).real
      {x : Fin N → 𝕂 | (toLp 2 x : EuclideanSpace 𝕂 (Fin N)) ∈ S} *
    (Measure.pi (fun _ : Fin N => κ)).real
      {x : Fin N → 𝕂 | (toLp 2 x : EuclideanSpace 𝕂 (Fin N)) ∈ T} ≤
    Real.exp (-(1/4)*t^2)
  rw [← talagrandEuclideanProductLaw_real κ N S hSm,
    ← talagrandEuclideanProductLaw_real κ N T hTm,
    ← hEqS, ← hEqT]
  exact hcompact

#print axioms cutoff_talagrand_hull_proved
end SpectralRadiusUpperTail

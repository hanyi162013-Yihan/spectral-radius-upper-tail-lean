import SpectralRadiusUpperTail.TalagrandHullGeometry
import SpectralRadiusUpperTail.CutoffConvexSeparation

namespace SpectralRadiusUpperTail
open MeasureTheory WithLp
variable {𝕂 : Type*} [RCLike 𝕂]

/-- The remaining distribution-free product-measure theorem, specialized to
the bounded cutoff laws. The constant 1/4 is the usual convex-distance form.
This definition records a hypothesis; it does not introduce an axiom. -/
def CutoffTalagrandHull (μ : Measure 𝕂) : Prop :=
  ∀ K N : ℕ, TalagrandHullSeparation
    (Measure.pi (fun _ : Fin N => μ.map (entryCutoff (K : ℝ))))
    (fun x : Fin N → 𝕂 => toLp 2 x) (1/4)

lemma cutoff_separation_of_talagrand (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hT : CutoffTalagrandHull μ) : CutoffConvexSeparation μ := by
  intro K
  letI : IsProbabilityMeasure (μ.map (entryCutoff (K : ℝ))) :=
    Measure.isProbabilityMeasure_map (entryCutoff_measurable (K : ℝ)).aemeasurable
  refine ⟨(1/4)/(2*((K : ℝ)+1))^2, by positivity, ?_⟩
  intro N
  apply convex_set_separation_of_hull _ (fun x : Fin N → 𝕂 => toLp 2 x)
    (K : ℝ) (1/4) (by positivity) ?_ (hT K N)
  change ∀ᵐ x ∂Measure.pi (fun _ : Fin N => μ.map (entryCutoff (K : ℝ))), ∀ i, ‖x i‖ ≤ (K : ℝ)
  apply ae_all_iff.mpr
  intro i
  exact (measurePreserving_eval (fun _ : Fin N => μ.map (entryCutoff (K : ℝ))) i).quasiMeasurePreserving.ae
    (entryCutoff_law_supported μ (K : ℝ) (by positivity))

/-- Every deterministic, median, centering and dimension-scaling step from
Talagrand convex distance to the required bounded convex concentration is proved. -/
lemma cutoff_concentration_of_talagrand (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hT : CutoffTalagrandHull μ) : CutoffConvexConcentration μ :=
  cutoff_concentration_of_separation μ (cutoff_separation_of_talagrand μ hT)

#print axioms cutoff_separation_of_talagrand
#print axioms cutoff_concentration_of_talagrand
end SpectralRadiusUpperTail

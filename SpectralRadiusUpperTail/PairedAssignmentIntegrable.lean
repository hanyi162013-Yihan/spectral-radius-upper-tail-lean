import SpectralRadiusUpperTail.PairedAssignmentMoment

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
variable {k n : ℕ}

lemma pairedAssignment_integrable (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c)
    (hexp : Integrable (fun z : 𝕂 => Real.exp (c*‖z‖^2)) μ)
    (x : (Fin (k+1) ⊕ Fin (k+1)) → Fin n) :
    Integrable (fun y : Fin n × Fin n → 𝕂 =>
      (∏ a : Fin k, y (x (Sum.inl a.castSucc),x (Sum.inl a.succ))) *
      (∏ a : Fin k, star (y (x (Sum.inr a.castSucc),x (Sum.inr a.succ)))))
      (Measure.pi (fun _ : Fin n × Fin n => μ)) := by
  simp_rw [entryWord_pair_eq_mixed]
  exact iidMixedProduct_integrable μ c hc hexp _ _

#print axioms pairedAssignment_integrable
end SpectralRadiusUpperTail

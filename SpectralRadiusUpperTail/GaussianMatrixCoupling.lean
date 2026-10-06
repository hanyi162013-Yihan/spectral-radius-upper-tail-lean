import SpectralRadiusUpperTail.GaussianRegressionMatrix

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂] {N : ℕ}

/-- The product of the actual sequential row couplings has the complete
actual tilted matrix source and the complete original iid comparator array. -/
theorem gaussianTiltedMatrix_coupling_exists (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (hm : (∫ x : 𝕂, x ∂μ) = 0)
    (hvar : (∫ x : 𝕂, ‖x‖^2 ∂μ) = 1) (v : ℕ → 𝕂)
    (hv : ∑ j : Fin N, ‖v j.val‖^2 ≤ 1) (a : ℝ) (ha : 0 < a) (t : Fin N → 𝕂) :
    ∃ Γ : Measure (Fin N → Fin N → 𝕂 × 𝕂), IsProbabilityMeasure Γ ∧
      Γ.map (fun x i => coordinateVector Prod.fst N (x i)) = gaussianTiltedMatrixLaw μ a v t ∧
      Γ.map (fun x i => comparatorVector N (x i)) =
        Measure.pi (fun _ : Fin N => Measure.pi (fun _ : Fin N => μ)) := by
  choose Γ hΓ hsource hcomparator using (fun i : Fin N => gaussianRow_coupling_exists μ v a ha N (t i))
  have (i : Fin N) : IsProbabilityMeasure (Γ i) := hΓ i
  have hfst : Measurable (coordinateVector (@Prod.fst 𝕂 𝕂) N) :=
    measurable_coordinateVector Prod.fst measurable_fst N
  have hsnd : Measurable (comparatorVector (α := 𝕂) N) :=
    measurable_coordinateVector Prod.snd measurable_snd N
  have (i : Fin N) : IsProbabilityMeasure ((Γ i).map (coordinateVector (@Prod.fst 𝕂 𝕂) N)) :=
    Measure.isProbabilityMeasure_map hfst.aemeasurable
  have (i : Fin N) : IsProbabilityMeasure ((Γ i).map (comparatorVector N)) :=
    Measure.isProbabilityMeasure_map hsnd.aemeasurable
  refine ⟨Measure.pi Γ, inferInstance, ?_, ?_⟩
  · rw [Measure.pi_map_pi (fun _ => hfst.aemeasurable)]
    unfold gaussianTiltedMatrixLaw
    congr 1
    funext i
    rw [hsource i, gaussianFiniteRowLaw_eq_coupling_source μ hX hm hvar v N hv a ha]
  · rw [Measure.pi_map_pi (fun _ => hsnd.aemeasurable)]
    congr 1
    funext i
    exact hcomparator i

#print axioms gaussianTiltedMatrix_coupling_exists
end SpectralRadiusUpperTail

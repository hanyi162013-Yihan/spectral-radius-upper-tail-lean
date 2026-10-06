import SpectralRadiusUpperTail.HaarSphereDirection
import SpectralRadiusUpperTail.FlatUnitDirections
import SpectralRadiusUpperTail.ConditionedSubtypeMeasure

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory Metric WithLp
open scoped BigOperators ENNReal
variable (𝕂 : Type*) [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]

noncomputable def haarDirectionLaw (n : ℕ) : Measure (Fin n → 𝕂) :=
  (haarSphereProbability (volume : Measure (EuclideanSpace 𝕂 (Fin n)))).map
    (fun v => ofLp v.val)

lemma haarDirectionLaw_probability (n : ℕ) (hn : 0 < n) :
    IsProbabilityMeasure (haarDirectionLaw 𝕂 n) := by
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  letI := haarSphereProbability_probability (volume : Measure (EuclideanSpace 𝕂 (Fin n)))
  exact Measure.isProbabilityMeasure_map (by fun_prop)

lemma flatUnitDirections_measurableSet (n : ℕ) (L : ℝ) :
    MeasurableSet (flatUnitDirections 𝕂 n L) := by
  unfold flatUnitDirections
  simp only [Set.setOf_and]
  apply MeasurableSet.inter (measurableSet_le (by fun_prop) measurable_const)
  apply MeasurableSet.inter
  · by_cases hn : 0 < n
    · simp only [hn,true_implies]
      exact measurableSet_eq_fun (by fun_prop) measurable_const
    · simp only [hn,false_implies,Set.setOf_true]
      exact MeasurableSet.univ
  · simp only [Set.setOf_forall]
    apply MeasurableSet.iInter
    intro i
    exact measurableSet_le (by fun_prop) measurable_const

lemma haarDirectionLaw_flat_mass (n : ℕ) (L : ℝ) :
    (haarDirectionLaw 𝕂 n).real (flatUnitDirections 𝕂 n L) =
      (haarSphereProbability (volume : Measure (EuclideanSpace 𝕂 (Fin n)))).real
        {v | ∀ i : Fin n, ‖v.val i‖ ≤ L/Real.sqrt (n : ℝ)} := by
  rw [haarDirectionLaw,map_measureReal_apply (by fun_prop) (flatUnitDirections_measurableSet 𝕂 n L)]
  congr 1
  ext v
  have hv : ‖v.val‖ = 1 := mem_sphere_zero_iff_norm.mp v.property
  have he : (∑ i : Fin n, ‖v.val i‖^2) = 1 := by
    rw [← EuclideanSpace.norm_sq_eq,hv]
    norm_num
  simp only [Set.mem_preimage,flatUnitDirections,Set.mem_setOf_eq,he,le_refl,true_and,
    implies_true]

noncomputable def haarFlatPrior (n : ℕ) (L : ℝ) (hL : 1 ≤ L) :
    Measure (flatUnitDirections 𝕂 n L) :=
  if h : 0 < n ∧ (haarDirectionLaw 𝕂 n) (flatUnitDirections 𝕂 n L) ≠ 0 then
    conditionedSubtypeMeasure (haarDirectionLaw 𝕂 n) (flatUnitDirections 𝕂 n L)
  else Measure.dirac ⟨(flatUnitDirections_nonempty 𝕂 n L hL).choose,
    (flatUnitDirections_nonempty 𝕂 n L hL).choose_spec⟩

lemma haarFlatPrior_probability (n : ℕ) (L : ℝ) (hL : 1 ≤ L) :
    IsProbabilityMeasure (haarFlatPrior 𝕂 n L hL) := by
  unfold haarFlatPrior
  split_ifs with h
  · letI := haarDirectionLaw_probability 𝕂 n h.1
    exact conditionedSubtypeMeasure_probability _ _ (flatUnitDirections_measurableSet 𝕂 n L) h.2
  · infer_instance

lemma haarFlatPrior_eq_conditioned (n : ℕ) (L : ℝ) (hL : 1 ≤ L) (hn : 0 < n)
    (hm : (haarDirectionLaw 𝕂 n) (flatUnitDirections 𝕂 n L) ≠ 0) :
    haarFlatPrior 𝕂 n L hL =
      conditionedSubtypeMeasure (haarDirectionLaw 𝕂 n) (flatUnitDirections 𝕂 n L) := by
  unfold haarFlatPrior
  exact dif_pos ⟨hn,hm⟩

#print axioms haarDirectionLaw
#print axioms haarDirectionLaw_probability
#print axioms flatUnitDirections_measurableSet
#print axioms haarDirectionLaw_flat_mass
#print axioms haarFlatPrior
#print axioms haarFlatPrior_probability
#print axioms haarFlatPrior_eq_conditioned
end SpectralRadiusUpperTail

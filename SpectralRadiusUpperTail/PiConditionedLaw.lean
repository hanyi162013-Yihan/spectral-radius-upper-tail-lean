import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Constructions.Pi

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

lemma pi_conditioned_law {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] (S : Set E) (hS : MeasurableSet S) (n : ℕ) :
    Measure.pi (fun _ : Fin n => μ[|S]) =
      (μ S)⁻¹^n • (Measure.pi (fun _ : Fin n => μ)).restrict (Set.univ.pi (fun _ : Fin n => S)) := by
  apply Measure.pi_eq
  intro s hs
  rw [Measure.smul_apply,Measure.restrict_apply (MeasurableSet.univ_pi hs)]
  have he : Set.univ.pi s ∩ Set.univ.pi (fun _ : Fin n => S) =
      Set.univ.pi (fun i => s i ∩ S) := by
    ext x
    simp only [Set.mem_inter_iff,Set.mem_pi,Set.mem_univ,true_implies]
    exact ⟨fun h i => ⟨h.1 i,h.2 i⟩,fun h => ⟨fun i => (h i).1,fun i => (h i).2⟩⟩
  rw [he,Measure.pi_pi]
  simp only [ProbabilityTheory.cond,Measure.smul_apply,Measure.restrict_apply (hs _),smul_eq_mul]
  rw [Finset.prod_mul_distrib]
  simp

lemma pi_conditioned_event {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] (S : Set E) (hS : MeasurableSet S) (n : ℕ)
    (A : Set (Fin n → E)) (hA : MeasurableSet A) :
    (Measure.pi (fun _ : Fin n => μ[|S])) A =
      (Measure.pi (fun _ : Fin n => μ)) (A ∩ Set.univ.pi (fun _ : Fin n => S))/(μ S)^n := by
  rw [pi_conditioned_law μ S hS n,Measure.smul_apply,Measure.restrict_apply hA]
  simp only [ENNReal.inv_pow,smul_eq_mul,div_eq_mul_inv,mul_comm]

#print axioms pi_conditioned_law
#print axioms pi_conditioned_event
end SpectralRadiusUpperTail

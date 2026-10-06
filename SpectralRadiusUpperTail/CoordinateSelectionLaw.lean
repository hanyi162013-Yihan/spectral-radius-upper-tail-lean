import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory

lemma coordinate_selection_law {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (n : ℕ) (I : Finset (Fin n)) :
    ((Measure.pi (fun _ : Fin n => μ)).prod (Measure.pi (fun _ : Fin n => ν))).map
      (fun p : (Fin n → α) × (Fin n → α) => fun j => if j ∈ I then p.1 j else p.2 j) =
      Measure.pi (fun j : Fin n => if j ∈ I then μ else ν) := by
  let e := MeasurableEquiv.arrowProdEquivProdArrow α α (Fin n)
  have hp := measurePreserving_arrowProdEquivProdArrow α α (Fin n) (fun _ => μ) (fun _ => ν)
  have hsel : Measurable (fun p : (Fin n → α) × (Fin n → α) =>
      fun j => if j ∈ I then p.1 j else p.2 j) := by
    apply measurable_pi_lambda
    intro j
    by_cases hj : j ∈ I <;> simp only [hj, if_true, if_false] <;> fun_prop
  rw [← hp.map_eq, Measure.map_map hsel e.measurable]
  let f : Fin n → α × α → α := fun j p => if j ∈ I then p.1 else p.2
  have hf (j : Fin n) : Measurable (f j) := by
    dsimp [f]
    by_cases hj : j ∈ I <;> simp only [hj, if_true, if_false] <;> fun_prop
  letI (j : Fin n) : IsProbabilityMeasure ((μ.prod ν).map (f j)) :=
    Measure.isProbabilityMeasure_map (hf j).aemeasurable
  change (Measure.pi (fun _ : Fin n => μ.prod ν)).map (fun p j => f j (p j)) = _
  rw [Measure.pi_map_pi (fun j => (hf j).aemeasurable)]
  congr 1
  funext j
  dsimp [f]
  by_cases hj : j ∈ I <;> simp [hj]

#print axioms coordinate_selection_law
end SpectralRadiusUpperTail

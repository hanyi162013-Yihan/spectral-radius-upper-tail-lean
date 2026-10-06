import SpectralRadiusUpperTail.IidIndexEmbedding
import Mathlib.Tactic.FunProp

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators

lemma iid_rectangular_flatten_law {ι κ K : Type*} [Fintype ι] [Fintype κ]
    [MeasurableSpace K] (μ : Measure K) [IsProbabilityMeasure μ] :
    (Measure.pi (fun _ : ι => Measure.pi (fun _ : κ => μ))).map
      (fun x : ι → κ → K => fun ij : ι × κ => x ij.1 ij.2) =
      Measure.pi (fun _ : ι × κ => μ) := by
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply (by fun_prop) (MeasurableSet.univ_pi hs)]
  have he : (fun x : ι → κ → K => fun ij : ι × κ => x ij.1 ij.2) ⁻¹'
      Set.pi Set.univ s = Set.pi Set.univ (fun i => Set.pi Set.univ (fun j => s (i,j))) := by
    ext x
    simp [Set.mem_pi, Prod.forall]
  rw [he, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  exact (Fintype.prod_prod_type (fun ij : ι × κ => μ (s ij))).symm

lemma iid_rectangular_curry_law {ι κ K : Type*} [Fintype ι] [Fintype κ]
    [MeasurableSpace K] (μ : Measure K) [IsProbabilityMeasure μ] :
    (Measure.pi (fun _ : ι × κ => μ)).map
      (fun x : ι × κ → K => fun i j => x (i,j)) =
      Measure.pi (fun _ : ι => Measure.pi (fun _ : κ => μ)) := by
  rw [← iid_rectangular_flatten_law μ, Measure.map_map (by fun_prop) (by fun_prop)]
  simp only [Function.comp_def, Measure.map_id']

/-- An injective rectangular selection from one iid array has the full
nested product law. This also covers overlapping selections across different paths. -/
lemma iid_rectangular_embedding_law {σ ι κ K : Type*} [Fintype σ] [Fintype ι] [Fintype κ]
    [MeasurableSpace K] (μ : Measure K) [IsProbabilityMeasure μ]
    (e : ι × κ → σ) (he : Function.Injective e) :
    (Measure.pi (fun _ : σ => μ)).map (fun x : σ → K => fun i j => x (e (i,j))) =
      Measure.pi (fun _ : ι => Measure.pi (fun _ : κ => μ)) := by
  have h := congrArg (fun ν : Measure (ι × κ → K) =>
    ν.map (fun x => fun i j => x (i,j))) (iidIndexEmbedding_law μ e he)
  rw [Measure.map_map (by fun_prop) (by fun_prop), iid_rectangular_curry_law] at h
  exact h

#print axioms iid_rectangular_embedding_law
end SpectralRadiusUpperTail

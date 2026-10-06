import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic.FunProp

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators

/-- The nested iid row law is exactly the iid entry law after flattening indices. -/
lemma iid_matrix_flatten_law {𝕂 : Type*} [MeasurableSpace 𝕂]
    (μ : Measure 𝕂) [IsProbabilityMeasure μ] (N : ℕ) :
    (Measure.pi (fun _ : Fin N => Measure.pi (fun _ : Fin N => μ))).map
      (fun x : Fin N → Fin N → 𝕂 => fun ij : Fin N × Fin N => x ij.1 ij.2) =
      Measure.pi (fun _ : Fin N × Fin N => μ) := by
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply (by fun_prop) (MeasurableSet.univ_pi hs)]
  have he : (fun x : Fin N → Fin N → 𝕂 => fun ij : Fin N × Fin N => x ij.1 ij.2) ⁻¹'
      Set.pi Set.univ s = Set.pi Set.univ (fun i => Set.pi Set.univ (fun j => s (i,j))) := by
    ext x
    simp [Set.mem_pi, Prod.forall]
  rw [he, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  exact (Fintype.prod_prod_type (fun ij : Fin N × Fin N => μ (s ij))).symm

#print axioms iid_matrix_flatten_law
end SpectralRadiusUpperTail

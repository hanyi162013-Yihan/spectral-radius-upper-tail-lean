import SpectralRadiusUpperTail.GaussianChainMoment
import SpectralRadiusUpperTail.SchurMatrixPathSum
import SpectralRadiusUpperTail.IidRectangularArray

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators Matrix.Norms.Frobenius

lemma schurPathEntry_injective {n d : ℕ} (p : AnyIncreasingPath n) :
    Function.Injective (fun z : Fin p.1 × (Fin d × Fin d) =>
      (increasingPathEdge p.2.val z.1, z.2)) := by
  intro z w h
  apply Prod.ext
  · exact increasingPathEdge_injective p.2.property (congrArg Prod.fst h)
  · exact congrArg (fun z : (Fin n × Fin n) × (Fin d × Fin d) => z.2) h

/-- A path selected from the common Gaussian array has the same second
moment as a fresh independent chain. No independence between paths is asserted. -/
theorem schurPathMatrix_second_moment {n d : ℕ} (p : AnyIncreasingPath n)
    (D : Fin (p.1+1) → Matrix (Fin d) (Fin d) ℝ) :
    Integrable (fun x : SchurEntryIndex n d → ℝ => ‖schurPathMatrix p D x‖^2)
      (Measure.pi (fun _ => standardNormal)) ∧
    (∫ x : SchurEntryIndex n d → ℝ, ‖schurPathMatrix p D x‖^2
      ∂Measure.pi (fun _ => standardNormal)) = ∏ i, ‖D i‖^2 := by
  have hp : MeasurePreserving
      (fun x : SchurEntryIndex n d → ℝ => fun j rs => x (increasingPathEdge p.2.val j, rs))
      (Measure.pi (fun _ => standardNormal))
      (Measure.pi (fun _ : Fin p.1 => Measure.pi (fun _ : Fin d × Fin d => standardNormal))) :=
    ⟨by fun_prop, iid_rectangular_embedding_law standardNormal _ (schurPathEntry_injective p)⟩
  have hm := gaussian_matrix_chain_second_moment (d := d) 1 p.1 D
  have hi := hp.integrable_comp_of_integrable hm.1
  have he := integral_map hp.measurable.aemeasurable (hp.map_eq.symm ▸ hm.1.aestronglyMeasurable)
  rw [hp.map_eq] at he
  have heq (x : SchurEntryIndex n d → ℝ) :
      gaussianMatrixChain d p.1 D (fun j => gaussianEntryBlock
        (fun rs => x (increasingPathEdge p.2.val j, rs))) = schurPathMatrix p D x := by
    unfold schurPathMatrix
    congr 1
  constructor
  · simpa only [Function.comp_def, one_smul, heq] using hi
  · have hh := he.symm.trans hm.2
    simpa only [one_smul, one_pow, one_mul, heq] using hh

#print axioms schurPathMatrix_second_moment
end SpectralRadiusUpperTail

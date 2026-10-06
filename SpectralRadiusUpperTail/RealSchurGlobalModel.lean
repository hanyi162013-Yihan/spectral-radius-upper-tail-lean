import SpectralRadiusUpperTail.RealSchurWaitingMoment
import SpectralRadiusUpperTail.SchurMatrixPathSum
import SpectralRadiusUpperTail.GaussianBridgeArray
import SpectralRadiusUpperTail.IidRectangularArray
import SpectralRadiusUpperTail.IndependentCoordinateSelection

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators Matrix.Norms.Frobenius

/-- One common array for every diagonal block and every Gaussian bridge block. -/
noncomputable def realSchurGlobalLaw {N : ℕ} (n : ℕ) (B : Fin N → RealSchurBlockData) :
    Measure ((Fin N → ℝ) × (SchurEntryIndex N 2 → ℝ)) :=
  (Measure.pi (fun i => realSchurDataLaw n (B i))).prod
    (Measure.pi (fun _ => standardNormal))

def realSchurSelectPath {N : ℕ} (p : AnyIncreasingPath N)
    (z : (Fin N → ℝ) × (SchurEntryIndex N 2 → ℝ)) :
    (Fin (p.1+1) → ℝ) × GaussianBridgeSpace 2 p.1 :=
  ((fun i => z.1 (p.2.val i)), gaussianBridgeFromArray 2 p.1
    (fun j rs => z.2 (increasingPathEdge p.2.val j, rs)))

lemma realSchurSelectPath_measurePreserving {N : ℕ} (n : ℕ) (hn : 0 < n)
    (B : Fin N → RealSchurBlockData) (hB : ∀ i, realSchurDataAdmissible (B i))
    (p : AnyIncreasingPath N) :
    MeasurePreserving (realSchurSelectPath p) (realSchurGlobalLaw n B)
      (realSchurPathLaw n p.1 (fun i => B (p.2.val i))) := by
  haveI (i : Fin N) := realSchurDataLaw_probability (n : ℝ) (Nat.cast_pos.mpr hn) (B i) (hB i)
  have hd : MeasurePreserving (fun s : Fin N → ℝ => fun i => s (p.2.val i))
      (Measure.pi (fun i => realSchurDataLaw n (B i)))
      (Measure.pi (fun i => realSchurDataLaw n (B (p.2.val i)))) :=
    ⟨by fun_prop, independent_coordinate_selection_law _ p.2.val p.2.property.injective⟩
  have heinj : Function.Injective (fun z : Fin p.1 × (Fin 2 × Fin 2) =>
      (increasingPathEdge p.2.val z.1, z.2)) := by
    intro z w h
    exact Prod.ext (increasingPathEdge_injective p.2.property (congrArg Prod.fst h))
      (congrArg (fun z : (Fin N × Fin N) × (Fin 2 × Fin 2) => z.2) h)
  have he : MeasurePreserving
      (fun x : SchurEntryIndex N 2 → ℝ => fun j rs => x (increasingPathEdge p.2.val j, rs))
      (Measure.pi (fun _ => standardNormal))
      (Measure.pi (fun _ : Fin p.1 => Measure.pi (fun _ : Fin 2 × Fin 2 => standardNormal))) :=
    ⟨by fun_prop, iid_rectangular_embedding_law standardNormal _ heinj⟩
  exact hd.prod ((gaussianBridgeFromArray_measurePreserving 2 p.1).comp he)

noncomputable def realSchurGlobalWaitingSum {N : ℕ} (n k : ℕ)
    (B : Fin N → RealSchurBlockData) (p : AnyIncreasingPath N)
    (z : (Fin N → ℝ) × (SchurEntryIndex N 2 → ℝ)) : Matrix (Fin 2) (Fin 2) ℝ :=
  realSchurWaitingSum n k p.1 (fun i => B (p.2.val i)) (realSchurSelectPath p z)

/-- The single-path waiting-time bound holds in the common global model,
so it can be combined with cross-path orthogonality in that same space. -/
theorem real_schur_global_waiting_second_moment {N : ℕ} (n k : ℕ) (hn : 0 < n)
    (η ρ : ℝ) (hη : 0 < η) (B : Fin N → RealSchurBlockData)
    (hB : ∀ i, realSchurDataAdmissible (B i)) (hmod : ∀ i, realSchurDataRadius (B i) ≤ ρ)
    (p : AnyIncreasingPath N) (hpk : p.1 ≤ k) :
    Integrable (fun z => ‖realSchurGlobalWaitingSum n k B p z‖^2) (realSchurGlobalLaw n B) ∧
    (∫ z, ‖realSchurGlobalWaitingSum n k B p z‖^2 ∂realSchurGlobalLaw n B) ≤
      (k.choose p.1 : ℝ)^2 * ((1/(n : ℝ))^p.1 *
        (2+2/((n : ℝ)*η^2))^(p.1+1)*(ρ+η)^(2*(k-p.1))) := by
  have hp := realSchurSelectPath_measurePreserving n hn B hB p
  have hm := real_schur_waiting_second_moment n k p.1 hn hpk η ρ hη
    (fun i => B (p.2.val i)) (fun i => hB (p.2.val i)) (fun i => hmod (p.2.val i))
  have hi := hp.integrable_comp_of_integrable hm.1
  have he := integral_map hp.measurable.aemeasurable (hp.map_eq.symm ▸ hm.1.aestronglyMeasurable)
  rw [hp.map_eq] at he
  exact ⟨hi, he.symm.le.trans hm.2⟩

#print axioms realSchurSelectPath_measurePreserving
#print axioms real_schur_global_waiting_second_moment
end SpectralRadiusUpperTail

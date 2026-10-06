import SpectralRadiusUpperTail.MatrixMoments
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory

/-- The iid Gaussian array law is invariant under every finite relabeling
of its coordinates. -/
theorem gaussianProductLaw_map_coordinate_permutation
    {ι : Type*} [Fintype ι] (e : ι ≃ ι) :
    (Measure.pi (fun _ : ι => standardNormal)).map
      (fun x : ι → ℝ => fun i => x (e.symm i)) =
        Measure.pi (fun _ : ι => standardNormal) := by
  have h := Measure.pi_map_piCongrLeft e
    (fun _ : ι => standardNormal)
  have hfun : (fun x : ι → ℝ => fun i => x (e.symm i)) =
      ⇑(MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e) := by
    funext x i
    have hv := MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : ι => ℝ) e x (e.symm i)
    simpa only [Equiv.apply_symm_apply] using hv.symm
  rw [hfun]
  simpa using h

/-- In particular, transposing an iid Gaussian matrix preserves its law. -/
theorem gaussianMatrixLaw_map_transpose (n : ℕ) :
    (gaussianMatrixLaw n).map
      (fun x : (Fin n × Fin n) → ℝ =>
        fun ij => x (ij.2, ij.1)) = gaussianMatrixLaw n := by
  let e : (Fin n × Fin n) ≃ (Fin n × Fin n) := Equiv.prodComm _ _
  have hfun : (fun x : (Fin n × Fin n) → ℝ =>
      fun ij => x (ij.2, ij.1)) =
      (fun x : (Fin n × Fin n) → ℝ =>
        fun ij => x (e.symm ij)) := by
    funext x ij
    cases ij
    rfl
  rw [hfun]
  exact gaussianProductLaw_map_coordinate_permutation e

#print axioms gaussianProductLaw_map_coordinate_permutation
#print axioms gaussianMatrixLaw_map_transpose
end SpectralRadiusUpperTail

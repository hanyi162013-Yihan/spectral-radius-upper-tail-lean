import SpectralRadiusUpperTail.GaussianProductPermutation
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory

/-- Relabeling both indices of the actual iid real-Gaussian matrix gives
the iid Gaussian law on the mixed block coordinate type. -/
theorem gaussianMatrixLaw_map_reindex
    {n : ℕ} {ι : Type*} [Fintype ι] (e : Fin n ≃ ι) :
    (gaussianMatrixLaw n).map
      (fun a : (Fin n × Fin n) → ℝ =>
        fun ij : ι × ι => a (e.symm ij.1, e.symm ij.2)) =
      Measure.pi (fun _ : ι × ι => standardNormal) := by
  let p : (Fin n × Fin n) ≃ (ι × ι) := Equiv.prodCongr e e
  have hfun : (fun a : (Fin n × Fin n) → ℝ =>
        fun ij : ι × ι => a (e.symm ij.1, e.symm ij.2)) =
      (fun a : (Fin n × Fin n) → ℝ =>
        fun ij : ι × ι => a (p.symm ij)) := by
    funext a ij
    rfl
  have hfun' : (fun a : (Fin n × Fin n) → ℝ =>
        fun ij : ι × ι => a (p.symm ij)) =
      ⇑(MeasurableEquiv.piCongrLeft (fun _ : ι × ι => ℝ) p) := by
    funext a ij
    have hv := MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : ι × ι => ℝ) p a (p.symm ij)
    simpa only [Equiv.apply_symm_apply] using hv.symm
  rw [hfun, hfun']
  simpa [gaussianMatrixLaw] using
    (Measure.pi_map_piCongrLeft p
      (fun _ : ι × ι => standardNormal))

#print axioms gaussianMatrixLaw_map_reindex
end SpectralRadiusUpperTail

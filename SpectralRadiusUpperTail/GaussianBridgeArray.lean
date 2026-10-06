import SpectralRadiusUpperTail.GaussianBridgeModel

namespace SpectralRadiusUpperTail
open MeasureTheory

/-- Arrange a finite iid array of Gaussian blocks as the recursive bridge space. -/
def gaussianBridgeFromArray (d : ℕ) : (l : ℕ) →
    (Fin l → Fin d × Fin d → ℝ) → GaussianBridgeSpace d l
  | 0, _ => ()
  | l+1, x => (gaussianBridgeFromArray d l (fun i => x i.castSucc), x (Fin.last l))

lemma gaussianBridgeFromArray_measurePreserving (d l : ℕ) :
    MeasurePreserving (gaussianBridgeFromArray d l)
      (Measure.pi (fun _ : Fin l => Measure.pi (fun _ : Fin d × Fin d => standardNormal)))
      (gaussianBridgeLaw d l) := by
  induction l with
  | zero =>
    constructor
    · exact measurable_const
    · change Measure.map (fun _ : Fin 0 → Fin d × Fin d → ℝ => ()) _ = Measure.dirac ()
      simp
  | succ l ih =>
    let ν := Measure.pi (fun _ : Fin d × Fin d => standardNormal)
    have hs := measurePreserving_piFinSuccAbove (fun _ : Fin (l+1) => ν) (Fin.last l)
    have ht : MeasurePreserving
        (fun x : Fin (l+1) → Fin d × Fin d → ℝ =>
          ((fun i : Fin l => x i.castSucc), x (Fin.last l)))
        (Measure.pi (fun _ : Fin (l+1) => ν))
        ((Measure.pi (fun _ : Fin l => ν)).prod ν) := by
      simpa only [Function.comp_def, MeasurableEquiv.piFinSuccAbove_apply,
        Fin.insertNthEquiv, Equiv.coe_fn_symm_mk, Prod.swap, Fin.removeNth_last, Fin.init_def,
        Fin.succAbove_last] using (Measure.measurePreserving_swap).comp hs
    exact (ih.prod (MeasurePreserving.id ν)).comp ht

#print axioms gaussianBridgeFromArray_measurePreserving
end SpectralRadiusUpperTail

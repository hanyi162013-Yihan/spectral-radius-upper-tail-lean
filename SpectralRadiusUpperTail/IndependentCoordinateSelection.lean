import SpectralRadiusUpperTail.IidIndexEmbedding
import Mathlib.Tactic.FunProp

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory

/-- Selecting distinct independent coordinates preserves their individual laws;
the coordinates need not have identical distributions. -/
lemma independent_coordinate_selection_law {σ τ K : Type*} [Fintype σ] [Fintype τ]
    [MeasurableSpace K] (μ : σ → Measure K) [∀ i, IsProbabilityMeasure (μ i)]
    (e : τ → σ) (he : Function.Injective e) :
    (Measure.pi μ).map (fun x : σ → K => fun i : τ => x (e i)) =
      Measure.pi (fun i : τ => μ (e i)) := by
  have hi : iIndepFun (fun i : σ => fun x : σ → K => x i) (Measure.pi μ) :=
    iIndepFun_pi (X := fun _ : σ => id) (fun _ => aemeasurable_id)
  have hs := hi.precomp he
  have hm := iIndepFun.map_fun_eq_pi_map
    (fun i : τ => (measurable_pi_apply (e i)).aemeasurable) hs
  calc
    _ = Measure.pi (fun i : τ => (Measure.pi μ).map (fun x : σ → K => x (e i))) := hm
    _ = _ := by
      congr 1
      funext i
      exact (measurePreserving_eval μ (e i)).map_eq

#print axioms independent_coordinate_selection_law
end SpectralRadiusUpperTail

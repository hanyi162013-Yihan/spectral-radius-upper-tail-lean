import Mathlib.Probability.Independence.Basic

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
variable {σ τ 𝕂 : Type*} [Fintype σ] [Fintype τ] [MeasurableSpace 𝕂]

/-- Restricting iid coordinates along an injective index map preserves the
 iid product law. -/
lemma iidIndexEmbedding_law (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (e : τ → σ) (he : Function.Injective e) :
    (Measure.pi (fun _ : σ => μ)).map (fun x : σ → 𝕂 => fun i : τ => x (e i)) =
      Measure.pi (fun _ : τ => μ) := by
  have hi : iIndepFun (fun i : σ => fun x : σ → 𝕂 => x i)
      (Measure.pi (fun _ : σ => μ)) :=
    iIndepFun_pi (X := fun _ : σ => id) (fun _ => aemeasurable_id)
  have hs := hi.precomp he
  have hm := iIndepFun.map_fun_eq_pi_map
    (fun i : τ => (measurable_pi_apply (e i)).aemeasurable) hs
  calc
    _ = Measure.pi (fun i : τ => (Measure.pi (fun _ : σ => μ)).map
        (fun x : σ → 𝕂 => x (e i))) := hm
    _ = _ := by
      congr 1
      funext i
      exact (measurePreserving_eval (fun _ : σ => μ) (e i)).map_eq

#print axioms iidIndexEmbedding_law
end SpectralRadiusUpperTail

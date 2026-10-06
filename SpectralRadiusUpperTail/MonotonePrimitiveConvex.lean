import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace SpectralRadiusUpperTail
open MeasureTheory Set
open scoped NNReal

lemma continuous_primitive_hasDerivAt (g : ℝ → ℝ) (hg : Continuous g) (x : ℝ) :
    HasDerivAt (fun s => ∫ t in (0 : ℝ)..s, g t) (g x) x :=
  intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable _ _)
    hg.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt

/-- A continuous increasing bounded nonnegative slope integrates to the exact
convex, monotone, Lipschitz package used by regularized singular-value sums. -/
lemma monotone_primitive_convex_package (g : ℝ → ℝ) (hg : Continuous g)
    (hm : MonotoneOn g (Ici 0)) (C : ℝ≥0)
    (hb : ∀ x : ℝ, 0 ≤ x → 0 ≤ g x ∧ g x ≤ (C : ℝ)) :
    ConvexOn ℝ (Ici 0) (fun s => ∫ t in (0 : ℝ)..s, g t) ∧
    MonotoneOn (fun s => ∫ t in (0 : ℝ)..s, g t) (Ici 0) ∧
    LipschitzOnWith C (fun s => ∫ t in (0 : ℝ)..s, g t) (Ici 0) := by
  have hd := continuous_primitive_hasDerivAt g hg
  have hc : Continuous (fun s => ∫ t in (0 : ℝ)..s, g t) :=
    (show Differentiable ℝ _ from fun x => (hd x).differentiableAt).continuous
  refine ⟨?_, ?_, ?_⟩
  · apply MonotoneOn.convexOn_of_deriv (convex_Ici 0) hc.continuousOn
      (fun x hx => (hd x).differentiableAt.differentiableWithinAt)
    intro x hx y hy hxy
    rw [(hd x).deriv, (hd y).deriv]
    exact hm (interior_subset hx) (interior_subset hy) hxy
  · apply monotoneOn_of_deriv_nonneg (convex_Ici 0) hc.continuousOn
      (fun x hx => (hd x).differentiableAt.differentiableWithinAt)
    intro x hx
    rw [(hd x).deriv]
    exact (hb x (interior_subset hx)).1
  · apply (convex_Ici (0 : ℝ)).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun x hx => (hd x).hasDerivWithinAt)
    intro x hx
    apply NNReal.coe_le_coe.mp
    change ‖g x‖ ≤ (C : ℝ)
    rw [Real.norm_eq_abs, abs_of_nonneg (hb x hx).1]
    exact (hb x hx).2

#print axioms continuous_primitive_hasDerivAt
#print axioms monotone_primitive_convex_package
end SpectralRadiusUpperTail

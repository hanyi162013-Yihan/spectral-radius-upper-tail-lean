import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped NNReal

lemma convex_even_extension (f : ℝ → ℝ) (hf : ConvexOn ℝ (Set.Ici 0) f)
    (hm : MonotoneOn f (Set.Ici 0)) : ConvexOn ℝ Set.univ (fun x : ℝ => f |x|) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have hbound : |a*x+b*y| ≤ a*|x|+b*|y| := by
    calc
      _ ≤ |a*x|+|b*y| := abs_add_le _ _
      _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
  have hpos : 0 ≤ a*|x|+b*|y| := by positivity
  have hx0 : |x| ∈ Set.Ici (0 : ℝ) := by simpa only [Set.mem_Ici] using abs_nonneg x
  have hy0 : |y| ∈ Set.Ici (0 : ℝ) := by simpa only [Set.mem_Ici] using abs_nonneg y
  have hz0 : |a*x+b*y| ∈ Set.Ici (0 : ℝ) := by
    simpa only [Set.mem_Ici] using abs_nonneg (a*x+b*y)
  have hw0 : a*|x|+b*|y| ∈ Set.Ici (0 : ℝ) := hpos
  exact (hm hz0 hw0 hbound).trans (hf.2 hx0 hy0 ha hb hab)

lemma lipschitz_even_extension (f : ℝ → ℝ) (C : ℝ≥0)
    (hf : LipschitzOnWith C f (Set.Ici 0)) : LipschitzWith C (fun x : ℝ => f |x|) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := hf.dist_le_mul |x| (by simpa only [Set.mem_Ici] using abs_nonneg x) |y| (by simpa only [Set.mem_Ici] using abs_nonneg y)
  have habs : dist |x| |y| ≤ dist x y := by
    simpa only [Real.dist_eq] using abs_abs_sub_abs_le_abs_sub x y
  exact h.trans (mul_le_mul_of_nonneg_left habs C.coe_nonneg)

#print axioms convex_even_extension
#print axioms lipschitz_even_extension
end SpectralRadiusUpperTail

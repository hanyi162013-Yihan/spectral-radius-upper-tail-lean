import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped BigOperators NNReal

noncomputable def euclideanComplexify (N : ℕ) : EuclideanSpace ℝ (Fin N) →ₗ[ℝ] EuclideanSpace ℂ (Fin N) where
  toFun x := WithLp.toLp 2 (fun i => (x i : ℂ))
  map_add' x y := by ext i; simp
  map_smul' a x := by ext i; simp [RCLike.real_smul_eq_coe_mul]

lemma euclideanComplexify_norm (N : ℕ) (x : EuclideanSpace ℝ (Fin N)) :
    ‖euclideanComplexify N x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i _
  change ‖(x i : ℂ)‖^2 = ‖x i‖^2
  rw [Complex.norm_real]

lemma convex_complexification_restrict (N : ℕ) (f : EuclideanSpace ℂ (Fin N) → ℝ)
    (hf : ConvexOn ℝ Set.univ f) :
    ConvexOn ℝ Set.univ (fun x => f (euclideanComplexify N x)) := by
  simpa only [Set.preimage_univ, Function.comp_def] using! hf.comp_linearMap (euclideanComplexify N)

lemma lipschitz_complexification_restrict (N : ℕ) (f : EuclideanSpace ℂ (Fin N) → ℝ)
    (C : ℝ≥0) (hf : LipschitzWith C f) :
    LipschitzWith C (fun x => f (euclideanComplexify N x)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hh := hf.dist_le_mul (euclideanComplexify N x) (euclideanComplexify N y)
  simpa only [dist_eq_norm, ← map_sub, euclideanComplexify_norm] using hh

#print axioms euclideanComplexify_norm
#print axioms convex_complexification_restrict
#print axioms lipschitz_complexification_restrict
end SpectralRadiusUpperTail

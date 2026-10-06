import SpectralRadiusUpperTail.DiscardedSquareMGF
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Lipschitz

namespace SpectralRadiusUpperTail
open MeasureTheory WithLp
open scoped BigOperators NNReal
variable {𝕂 : Type*} [RCLike 𝕂]

noncomputable def entryCutoff (R : ℝ) (z : 𝕂) : 𝕂 :=
  if ‖z‖ ≤ R then z else 0

lemma entryCutoff_measurable (R : ℝ) : Measurable (entryCutoff (𝕂 := 𝕂) R) := by
  unfold entryCutoff
  exact Measurable.ite (measurableSet_le measurable_norm measurable_const) measurable_id measurable_const

lemma entryCutoff_error_square (R : ℝ) (z : 𝕂) :
    ‖z-entryCutoff R z‖^2 = discardedSquare R z := by
  by_cases h : ‖z‖ ≤ R
  · simp [entryCutoff,discardedSquare,h,not_lt.mpr h]
  · simp [entryCutoff,discardedSquare,h,lt_of_not_ge h]

lemma arrayCutoff_error_norm_square (N : ℕ) (R : ℝ) (x : Fin N → 𝕂) :
    ‖toLp 2 x-toLp 2 (fun i => entryCutoff R (x i))‖^2 =
      ∑ i, discardedSquare R (x i) := by
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i hi
  exact entryCutoff_error_square R (x i)

lemma arrayCutoff_lipschitz_error (N : ℕ) (R : ℝ) (L : ℝ≥0)
    (f : EuclideanSpace 𝕂 (Fin N) → ℝ) (hf : LipschitzWith L f) (x : Fin N → 𝕂) :
    |f (toLp 2 x)-f (toLp 2 (fun i => entryCutoff R (x i)))| ≤
      (L : ℝ)*Real.sqrt (∑ i, discardedSquare R (x i)) := by
  have hh := hf.dist_le_mul (toLp 2 x) (toLp 2 (fun i => entryCutoff R (x i)))
  rw [Real.dist_eq,dist_eq_norm] at hh
  have he : ‖toLp 2 x-toLp 2 (fun i => entryCutoff R (x i))‖ =
      Real.sqrt (∑ i, discardedSquare R (x i)) := by
    rw [← arrayCutoff_error_norm_square N R x,Real.sqrt_sq (norm_nonneg _)]
  rwa [he] at hh

#print axioms entryCutoff
#print axioms entryCutoff_measurable
#print axioms entryCutoff_error_square
#print axioms arrayCutoff_error_norm_square
#print axioms arrayCutoff_lipschitz_error
end SpectralRadiusUpperTail

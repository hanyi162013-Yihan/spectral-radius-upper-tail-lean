import SpectralRadiusUpperTail.MatrixSingularConvexity
import SpectralRadiusUpperTail.EuclideanEntryMatrix

namespace SpectralRadiusUpperTail
open scoped BigOperators NNReal Matrix.Norms.Frobenius

noncomputable def normalizedSingularObservable (n : ℕ) (z : ℂ) (f : ℝ → ℝ)
    (x : EuclideanSpace ℂ (Fin (n*n))) : ℝ :=
  matrixSingularSum f (euclideanResidualMatrix n z x)/(n : ℝ)

lemma normalizedSingularObservable_convex (n : ℕ) (z : ℂ) (f : ℝ → ℝ)
    (hf : ConvexOn ℝ (Set.Ici 0) f) (hm : MonotoneOn f (Set.Ici 0)) :
    ConvexOn ℝ Set.univ (normalizedSingularObservable n z f) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have hh := (matrixSingularSum_convex n f hf hm).2
    (Set.mem_univ (euclideanResidualMatrix n z x))
    (Set.mem_univ (euclideanResidualMatrix n z y)) ha hb hab
  have hd := div_le_div_of_nonneg_right hh (Nat.cast_nonneg n)
  rw [← euclideanResidualMatrix_combination n z x y a b hab] at hd
  convert! hd using 1 <;> simp only [normalizedSingularObservable, smul_eq_mul] <;> ring

lemma normalizedSingularObservable_lipschitz (n : ℕ) (hn : 0 < n) (z : ℂ) (f : ℝ → ℝ)
    (hf : ConvexOn ℝ (Set.Ici 0) f) (hm : MonotoneOn f (Set.Ici 0))
    (C : ℝ≥0) (hLip : LipschitzOnWith C f (Set.Ici 0)) :
    LipschitzWith (C/(n : ℝ≥0)) (normalizedSingularObservable n z f) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hsqrt : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hnR)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hh := matrixSingularSum_lipschitz_bound f hf hm C hLip
    (euclideanResidualMatrix n z x) (euclideanResidualMatrix n z y)
  rw [euclideanResidualMatrix_norm_sub] at hh
  have hd := div_le_div_of_nonneg_right hh hnR.le
  have he : ((C : ℝ)*Real.sqrt (n : ℝ)*((1/Real.sqrt (n : ℝ))*‖x-y‖))/(n : ℝ) =
      ((C : ℝ)/(n : ℝ))*‖x-y‖ := by field_simp
  rw [he] at hd
  simpa only [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs, normalizedSingularObservable, ← sub_div,
    abs_div, abs_of_pos hnR, NNReal.coe_div, NNReal.coe_natCast] using hd

#print axioms normalizedSingularObservable_convex
#print axioms normalizedSingularObservable_lipschitz
end SpectralRadiusUpperTail

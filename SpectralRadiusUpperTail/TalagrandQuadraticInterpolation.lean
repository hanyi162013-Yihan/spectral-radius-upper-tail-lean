import SpectralRadiusUpperTail.CoordinateConvexHull

namespace SpectralRadiusUpperTail
open WithLp
open scoped BigOperators

lemma norm_sq_real_combination_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v w : E) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    ‖a • v+b • w‖^2 ≤ a*‖v‖^2+b*‖w‖^2 := by
  have hn : ‖a • v+b • w‖ ≤ a*‖v‖+b*‖w‖ := by
    simpa only [zero_sub, norm_neg] using norm_sub_real_combination_le (0 : E) v w a b ha hb hab
  have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ a*‖v‖+b*‖w‖)).mpr hn
  have he : (a*‖v‖+b*‖w‖)^2 = a*‖v‖^2+b*‖w‖^2-a*b*(‖v‖-‖w‖)^2 := by
    calc
      _ = (a+b)*(a*‖v‖^2+b*‖w‖^2)-a*b*(‖v‖-‖w‖)^2 := by ring
      _ = _ := by rw [hab, one_mul]
  rw [he] at hsq
  have hp : 0 ≤ a*b*(‖v‖-‖w‖)^2 := by positivity
  linarith

noncomputable def euclideanConsReal (N : ℕ) (t : ℝ) (v : EuclideanSpace ℝ (Fin N)) :
    EuclideanSpace ℝ (Fin (N+1)) := toLp 2 (Fin.cons t (fun i => v i))

lemma euclideanConsReal_norm_sq (N : ℕ) (t : ℝ) (v : EuclideanSpace ℝ (Fin N)) :
    ‖euclideanConsReal N t v‖^2 = t^2+‖v‖^2 := by
  simp [euclideanConsReal, EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ, Real.norm_eq_abs, sq_abs]

/-- The last-coordinate penalty in the Talagrand fiber interpolation is b²,
while the preceding coordinates retain a convex average of squared norms. -/
lemma talagrand_cons_interpolation_bound (N : ℕ) (v w : EuclideanSpace ℝ (Fin N))
    (a b t : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) (ht : |t| ≤ 1) :
    ‖euclideanConsReal N (b*t) (a • v+b • w)‖^2 ≤ a*‖v‖^2+b*‖w‖^2+b^2 := by
  rw [euclideanConsReal_norm_sq]
  have hn := norm_sq_real_combination_le v w a b ha hb hab
  have ht2 : t^2 ≤ 1 := by nlinarith [(abs_le.mp ht).1, (abs_le.mp ht).2]
  have hp := mul_le_mul_of_nonneg_left ht2 (sq_nonneg b)
  rw [mul_pow]
  nlinarith only [hn, hp]

#print axioms norm_sq_real_combination_le
#print axioms euclideanConsReal_norm_sq
#print axioms talagrand_cons_interpolation_bound
end SpectralRadiusUpperTail

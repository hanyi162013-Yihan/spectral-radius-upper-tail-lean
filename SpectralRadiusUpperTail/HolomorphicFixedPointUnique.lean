import SpectralRadiusUpperTail.HolomorphicNearConstant

namespace SpectralRadiusUpperTail
open Metric Set
open scoped NNReal

lemma holomorphic_near_constant_fixedPoint_unique (f : ℂ → ℂ) (b : ℂ) (d : ℝ) (hd : 0 < d)
    (hf : DifferentiableOn ℂ f (ball b (3*d)))
    (hmap : MapsTo f (ball b (3*d)) (closedBall b (d/8)))
    (x y : ℂ) (hx : x ∈ closedBall b d) (hy : y ∈ closedBall b d)
    (hfx : f x = x) (hfy : f y = y) : x = y := by
  have hinside : closedBall b d ⊆ ball b (3*d) := by
    intro z hz
    have hh : dist z b ≤ d := hz
    change dist z b < 3*d
    linarith
  have hlip : LipschitzOnWith (1/2 : ℝ≥0) f (closedBall b d) := by
    apply Convex.lipschitzOnWith_of_nnnorm_deriv_le
      (fun z hz => hf.differentiableAt (isOpen_ball.mem_nhds (hinside hz))) _ (convex_closedBall b d)
    intro z hz
    have hh := near_constant_deriv_bound f b d hd hf hmap z hz
    change ‖deriv f z‖ ≤ ((1/2 : ℝ≥0) : ℝ)
    norm_num
    linarith
  have he := hlip.dist_le_mul x hx y hy
  rw [hfx,hfy] at he
  norm_num at he
  apply dist_eq_zero.1
  linarith [dist_nonneg (x := x) (y := y)]

lemma holomorphic_near_constant_real_fixedPoint (f : ℂ → ℂ) (b d : ℝ) (hd : 0 < d)
    (hf : DifferentiableOn ℂ f (ball (b : ℂ) (3*d)))
    (hmap : MapsTo f (ball (b : ℂ) (3*d)) (closedBall (b : ℂ) (d/8)))
    (hsym : ∀ z, f (star z) = star (f z)) :
    ∃ z : ℝ, (z : ℂ) ∈ closedBall (b : ℂ) d ∧ f z = z := by
  obtain ⟨z,hz,hfix⟩ := holomorphic_near_constant_fixedPoint f b d hd hf hmap
  have hzstar : star z ∈ closedBall (b : ℂ) d := by
    have he : dist (star z) (b : ℂ) = dist z (b : ℂ) := by
      simpa only [Complex.star_def,Complex.conj_ofReal] using star_isometry.dist_eq z (b : ℂ)
    change dist (star z) (b : ℂ) ≤ d
    rw [he]
    exact hz
  have hstarfix : f (star z) = star z := by rw [hsym,hfix]
  have he := holomorphic_near_constant_fixedPoint_unique f b d hd hf hmap
    (star z) z hzstar hz hstarfix hfix
  obtain ⟨r,hr⟩ := Complex.conj_eq_iff_real.1 he
  exact ⟨r,by simpa only [hr] using hz,by simpa only [hr] using hfix⟩

#print axioms holomorphic_near_constant_fixedPoint_unique
#print axioms holomorphic_near_constant_real_fixedPoint
end SpectralRadiusUpperTail

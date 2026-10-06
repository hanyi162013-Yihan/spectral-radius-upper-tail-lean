import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Contracting

namespace SpectralRadiusUpperTail
open Metric Set
open scoped NNReal

lemma inner_ball_subset_triple (b x : ℂ) (d : ℝ) (hd : 0 < d)
    (hx : x ∈ closedBall b d) : ball x d ⊆ ball b (3*d) := by
  intro w hw
  have h1 : dist w x < d := hw
  have h2 : dist x b ≤ d := hx
  have h3 := dist_triangle w x b
  change dist w b < 3*d
  linarith

lemma near_constant_deriv_bound (f : ℂ → ℂ) (b : ℂ) (d : ℝ) (hd : 0 < d)
    (hf : DifferentiableOn ℂ f (ball b (3*d)))
    (hmap : MapsTo f (ball b (3*d)) (closedBall b (d/8)))
    (x : ℂ) (hx : x ∈ closedBall b d) : ‖deriv f x‖ ≤ 1/4 := by
  have hxB : x ∈ ball b (3*d) := by
    have hh : dist x b ≤ d := hx
    change dist x b < 3*d
    linarith
  have hlocal := inner_ball_subset_triple b x d hd hx
  have hmaps : MapsTo f (ball x d) (closedBall (f x) (d/4)) := by
    intro w hw
    have h1 : dist (f w) b ≤ d/8 := hmap (hlocal hw)
    have h2 : dist (f x) b ≤ d/8 := hmap hxB
    have h3 := dist_triangle (f w) b (f x)
    rw [dist_comm b (f x)] at h3
    change dist (f w) (f x) ≤ d/4
    linarith
  have hh := Complex.norm_deriv_le_div_of_mapsTo_ball (hf.mono hlocal) hmaps hd
  have he : (d/4)/d = (1:ℝ)/4 := by field_simp
  exact hh.trans_eq he

lemma holomorphic_near_constant_fixedPoint (f : ℂ → ℂ) (b : ℂ) (d : ℝ) (hd : 0 < d)
    (hf : DifferentiableOn ℂ f (ball b (3*d)))
    (hmap : MapsTo f (ball b (3*d)) (closedBall b (d/8))) :
    ∃ z ∈ closedBall b d, f z = z := by
  have hinside : closedBall b d ⊆ ball b (3*d) := by
    intro x hx
    have hh : dist x b ≤ d := hx
    change dist x b < 3*d
    linarith
  have hself : MapsTo f (closedBall b d) (closedBall b d) := by
    intro x hx
    have hh : dist (f x) b ≤ d/8 := hmap (hinside hx)
    change dist (f x) b ≤ d
    linarith
  have hlip : LipschitzOnWith (1/2 : ℝ≥0) f (closedBall b d) := by
    apply Convex.lipschitzOnWith_of_nnnorm_deriv_le
      (fun x hx => hf.differentiableAt (isOpen_ball.mem_nhds (hinside hx))) _ (convex_closedBall b d)
    intro x hx
    have hh := near_constant_deriv_bound f b d hd hf hmap x hx
    change ‖deriv f x‖ ≤ ((1/2 : ℝ≥0) : ℝ)
    norm_num
    linarith
  have hcontract : ContractingWith (1/2 : ℝ≥0) (hself.restrict f (closedBall b d) (closedBall b d)) :=
    ⟨by norm_num,hlip.mapsToRestrict hself⟩
  obtain ⟨z,hz,hfix,_⟩ := ContractingWith.exists_fixedPoint' isClosed_closedBall.isComplete hself
    hcontract (mem_closedBall_self hd.le) (edist_ne_top b (f b))
  exact ⟨z,hz,hfix⟩

#print axioms inner_ball_subset_triple
#print axioms near_constant_deriv_bound
#print axioms holomorphic_near_constant_fixedPoint
end SpectralRadiusUpperTail

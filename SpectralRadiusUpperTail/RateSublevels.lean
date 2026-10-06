import SpectralRadiusUpperTail.Rate
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open Set

lemma rate_at_one (β : ℝ) : rate β 1 = 0 := by simp [rate]

lemma rate_quadratic_lower (β r : ℝ) (hβ : 0 ≤ β) (hr : 0 < r) :
    (β/2)*(r-1)^2 ≤ rate β r := by
  have hl := Real.log_le_sub_one_of_pos hr
  have hh := mul_le_mul_of_nonneg_left hl hβ
  unfold rate
  nlinarith

lemma rate_coercive_on_upper_domain (β M : ℝ) (hβ : 0 < β) :
    ∃ R : ℝ, 1 < R ∧ ∀ r : ℝ, R ≤ r → M ≤ rate β r := by
  refine ⟨max 2 (1+2*M/β), by linarith [le_max_left (2 : ℝ) (1+2*M/β)], ?_⟩
  intro r hr
  have hr2 : 2 ≤ r := (le_max_left _ _).trans hr
  have hrM : 1+2*M/β ≤ r := (le_max_right _ _).trans hr
  have hm := (div_le_iff₀ hβ).mp (show 2*M/β ≤ r-1 by linarith)
  have hquad := rate_quadratic_lower β r hβ.le (by linarith)
  have hsq : r-1 ≤ (r-1)^2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hsq (show 0 ≤ β/2 by positivity)
  nlinarith

lemma continuous_clipped_rate (β : ℝ) : Continuous (fun r : ℝ => rate β (max 1 r)) := by
  have hpos (r : ℝ) : 0 < max 1 r := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  unfold rate
  have hlog : Continuous (fun r : ℝ => Real.log (max 1 r)) :=
    (continuous_const.max continuous_id).log (fun r => ne_of_gt (hpos r))
  fun_prop

lemma rate_upper_sublevel_closed (β M : ℝ) : IsClosed {r : ℝ | 1 ≤ r ∧ rate β r ≤ M} := by
  have he : {r : ℝ | 1 ≤ r ∧ rate β r ≤ M} =
      Ici 1 ∩ {r : ℝ | rate β (max 1 r) ≤ M} := by
    ext r
    change (1 ≤ r ∧ rate β r ≤ M) ↔ (1 ≤ r ∧ rate β (max 1 r) ≤ M)
    constructor
    · rintro ⟨hr, hI⟩
      exact ⟨hr, by simpa only [max_eq_right hr] using hI⟩
    · rintro ⟨hr, hI⟩
      exact ⟨hr, by simpa only [max_eq_right hr] using hI⟩
  rw [he]
  exact isClosed_Ici.inter (isClosed_le (continuous_clipped_rate β) continuous_const)

/-- The rate restricted to the upper-tail domain has compact sublevels. -/
lemma rate_upper_sublevel_compact (β M : ℝ) (hβ : 0 < β) :
    IsCompact {r : ℝ | 1 ≤ r ∧ rate β r ≤ M} := by
  obtain ⟨R, hR, hcoercive⟩ := rate_coercive_on_upper_domain β (M+1) hβ
  apply isCompact_Icc.of_isClosed_subset (rate_upper_sublevel_closed β M)
    (s := Icc 1 R)
  intro r hr
  refine ⟨hr.1, ?_⟩
  by_contra hn
  have hh := hcoercive r (le_of_not_ge hn)
  linarith [hr.2]

#print axioms rate_quadratic_lower
#print axioms rate_coercive_on_upper_domain
#print axioms continuous_clipped_rate
#print axioms rate_upper_sublevel_compact
end SpectralRadiusUpperTail

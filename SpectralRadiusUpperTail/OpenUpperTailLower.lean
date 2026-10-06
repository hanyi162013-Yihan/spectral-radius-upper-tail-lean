import SpectralRadiusUpperTail.TailIntervalBounds
import SpectralRadiusUpperTail.Rate
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

namespace SpectralRadiusUpperTail
open MeasureTheory Filter Set
open scoped Topology

lemma open_upper_neighborhood_interval (U : Set ℝ) (hU : IsOpen U)
    (x : ℝ) (hx : x ∈ U) (hx1 : 1 < x) :
    ∃ a b : ℝ, 1 < a ∧ a < x ∧ x < b ∧ Ioo a b ⊆ U := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  let a := max ((1+x)/2) (x-ε/2)
  let b := x+ε/2
  have ha1 : 1 < a := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hax : a < x := max_lt (by linarith) (by linarith)
  have hxb : x < b := by dsimp [b]; linarith
  refine ⟨a, b, ha1, hax, hxb, ?_⟩
  intro y hy
  apply hball
  change dist y x < ε
  rw [Real.dist_eq, abs_sub_lt_iff]
  have ha : x-ε/2 ≤ a := le_max_right _ _
  change a < y ∧ y < b at hy
  dsimp [b] at hy
  constructor <;> linarith

/-- The tail sandwich already gives the LDP lower estimate at every point
strictly above one, for every open neighborhood of that point. -/
lemma open_set_exponential_lower_above_one
    (Ω : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)]
    (μ : (n : ℕ) → Measure (Ω n)) [∀ n, IsFiniteMeasure (μ n)]
    (X : (n : ℕ) → Ω n → ℝ) (β : ℝ) (hβ : 0 < β)
    (htails : ∀ r : ℝ, 1 < r → ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      Real.exp ((n : ℝ)*(-rate β r-ε)) ≤ (μ n).real {x | r < X n x} ∧
      (μ n).real {x | r ≤ X n x} ≤ Real.exp ((n : ℝ)*(-rate β r+ε)))
    (U : Set ℝ) (hU : IsOpen U) (x : ℝ) (hx : x ∈ U) (hx1 : 1 < x)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, Real.exp ((n : ℝ)*(-rate β x-ε)) ≤ (μ n).real {ω | X n ω ∈ U} := by
  obtain ⟨a, b, ha, hax, hxb, hUab⟩ := open_upper_neighborhood_interval U hU x hx hx1
  have hab : a < b := hax.trans hxb
  have hIab := rate_strict_mono β a b hβ ha.le hab
  have hIax := rate_strict_mono β a x hβ ha.le hax
  have hl := interval_exponential_lower_of_tails Ω μ X a b (rate β a) (rate β b) hIab
    (fun δ hδ => (htails a ha δ hδ).mono (fun _ h => h.1))
    (fun δ hδ => (htails b (ha.trans hab) δ hδ).mono (fun _ h => h.2)) ε hε
  filter_upwards [hl] with n hn
  have he : Real.exp ((n : ℝ)*(-rate β x-ε)) ≤ Real.exp ((n : ℝ)*(-rate β a-ε)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg n))
  apply he.trans (hn.trans (measureReal_mono (μ := μ n) ?_ (measure_ne_top _ _)))
  intro ω hω
  exact hUab hω

/-- Infimum form of the open-set lower bound on the upper-tail domain. -/
lemma open_set_exponential_lower_rate_infimum
    (Ω : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)]
    (μ : (n : ℕ) → Measure (Ω n)) [∀ n, IsFiniteMeasure (μ n)]
    (X : (n : ℕ) → Ω n → ℝ) (β : ℝ) (hβ : 0 < β)
    (htails : ∀ r : ℝ, 1 < r → ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      Real.exp ((n : ℝ)*(-rate β r-ε)) ≤ (μ n).real {x | r < X n x} ∧
      (μ n).real {x | r ≤ X n x} ≤ Real.exp ((n : ℝ)*(-rate β r+ε)))
    (U : Set ℝ) (hU : IsOpen U) (hne : U.Nonempty) (h1 : ∀ r ∈ U, 1 < r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, Real.exp ((n : ℝ)*(-sInf (rate β '' U)-ε)) ≤
      (μ n).real {ω | X n ω ∈ U} := by
  have hIne : (rate β '' U).Nonempty := hne.image _
  obtain ⟨v, hv, hvlt⟩ := exists_lt_of_csInf_lt hIne
    (show sInf (rate β '' U) < sInf (rate β '' U)+ε/2 by linarith)
  obtain ⟨x, hx, rfl⟩ := hv
  filter_upwards [open_set_exponential_lower_above_one Ω μ X β hβ htails U hU x hx
    (h1 x hx) (ε/2) (by positivity)] with n hn
  apply le_trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg n))) hn
  linarith

#print axioms open_upper_neighborhood_interval
#print axioms open_set_exponential_lower_above_one
#print axioms open_set_exponential_lower_rate_infimum
end SpectralRadiusUpperTail

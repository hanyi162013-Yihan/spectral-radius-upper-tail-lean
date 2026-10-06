import SpectralRadiusUpperTail.OpenUpperTailLower
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

namespace SpectralRadiusUpperTail
open MeasureTheory Filter Set
open scoped Topology

lemma clipped_strict_tail {Ω : Type*} (X : Ω → ℝ) (r : ℝ) (hr : 1 < r) :
    {x | r < max 1 (X x)} = {x | r < X x} := by
  ext x
  simp only [mem_setOf_eq, lt_max_iff, not_lt.mpr hr.le, false_or]

lemma clipped_closed_tail {Ω : Type*} (X : Ω → ℝ) (r : ℝ) (hr : 1 < r) :
    {x | r ≤ max 1 (X x)} = {x | r ≤ X x} := by
  ext x
  simp only [mem_setOf_eq, le_max_iff, not_le.mpr hr, false_or]

lemma rate_infimum_support_at_one (β : ℝ) (hβ : 0 ≤ β) (U : Set ℝ) (hU : 1 ∈ U) :
    sInf (rate β '' (U ∩ Ici 1)) = 0 := by
  apply IsLeast.csInf_eq
  refine ⟨⟨1, ⟨hU, by change (1 : ℝ) ≤ 1; exact le_rfl⟩, by simp [rate]⟩, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact rate_nonneg β x hβ (lt_of_lt_of_le (by norm_num) hx.2)

/-- A neighborhood of the clipped radius one has rate zero, using only a
strictly positive sharp upper-tail rate. No lower-tail theorem is used. -/
lemma clipped_open_neighborhood_one
    (Ω : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)]
    (μ : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (X : (n : ℕ) → Ω n → ℝ) (β : ℝ) (hβ : 0 < β)
    (hupper : ∀ r : ℝ, 1 < r → ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      (μ n).real {x | r ≤ X n x} ≤ Real.exp ((n : ℝ)*(-rate β r+ε)))
    (U : Set ℝ) (hU : IsOpen U) (h1 : 1 ∈ U) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, Real.exp (-(n : ℝ)*ε) ≤ (μ n).real {ω | max 1 (X n ω) ∈ U} := by
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds h1)
  let r := 1+δ/2
  have hr : 1 < r := by dsimp [r]; linarith
  have hI : 0 < rate β r := rate_pos β r hβ hr
  have hmass (n : ℕ) : 1-(μ n).real {ω | r ≤ X n ω} ≤ (μ n).real {ω | max 1 (X n ω) ∈ U} := by
    have hsub : (univ : Set (Ω n)) ⊆ {ω | max 1 (X n ω) ∈ U} ∪ {ω | r ≤ X n ω} := by
      intro ω _
      by_cases hx : r ≤ X n ω
      · exact Or.inr hx
      · left
        apply hball
        change dist (max 1 (X n ω)) 1 < δ
        rw [Real.dist_eq, abs_sub_lt_iff]
        have hlo : 1 ≤ max 1 (X n ω) := le_max_left _ _
        have hhi : max 1 (X n ω) < r := max_lt hr (lt_of_not_ge hx)
        dsimp [r] at hhi
        constructor <;> linarith
    have hh := (measureReal_mono (μ := μ n) hsub (measure_ne_top _ _)).trans (measureReal_union_le _ _)
    rw [probReal_univ] at hh
    linarith
  filter_upwards [hupper r hr (rate β r/2) (by positivity),
    eventually_exponential_difference_lower 0 (-rate β r/2) ε (by linarith) hε] with n hn hd
  have he : (n : ℝ)*(-rate β r+rate β r/2) = (n : ℝ)*(-rate β r/2) := by ring
  rw [he] at hn
  have he' : (n : ℝ)*(0-ε) = -(n : ℝ)*ε := by ring
  rw [he', mul_zero, Real.exp_zero] at hd
  linarith [hmass n]

#print axioms clipped_strict_tail
#print axioms clipped_closed_tail
#print axioms rate_infimum_support_at_one
#print axioms clipped_open_neighborhood_one
end SpectralRadiusUpperTail

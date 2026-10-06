import SpectralRadiusUpperTail.BoundedMedianRange
import Mathlib.Analysis.Convex.Function

namespace SpectralRadiusUpperTail
open MeasureTheory Set
open scoped NNReal

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A geometric form of the remaining Talagrand input. Only closed convex
sublevel sets are needed; the measure may be presented through coordinates X. -/
def ConvexSetSeparation (μ : Measure Ω) (X : Ω → E) (q : ℝ) : Prop :=
  ∀ A B : Set E, IsClosed A → Convex ℝ A → IsClosed B →
    ∀ t : ℝ, 0 ≤ t → (∀ a ∈ A, ∀ b ∈ B, t ≤ dist a b) →
      μ.real (X ⁻¹' A)*μ.real (X ⁻¹' B) ≤ Real.exp (-q*t^2)

lemma convex_sublevel_separation_bound (μ : Measure Ω) (X : Ω → E)
    (q : ℝ) (hsep : ConvexSetSeparation μ X q) (C : ℝ≥0) (hC : 0 < (C : ℝ))
    (f : E → ℝ) (hfc : ConvexOn ℝ univ f) (hf : LipschitzWith C f)
    (a b : ℝ) (hab : a ≤ b) :
    μ.real {x | f (X x) ≤ a}*μ.real {x | b ≤ f (X x)} ≤
      Real.exp (-q*((b-a)/(C : ℝ))^2) := by
  have hA : Convex ℝ {x | f x ≤ a} := by simpa only [mem_univ, true_and] using hfc.convex_le a
  apply hsep {x | f x ≤ a} {x | b ≤ f x}
    (isClosed_le hf.continuous continuous_const) hA
    (isClosed_le continuous_const hf.continuous) ((b-a)/(C : ℝ)) (by positivity)
  intro x hx y hy
  apply (div_le_iff₀ hC).mpr
  have hh := hf.dist_le_mul y x
  rw [Real.dist_eq, dist_comm y x] at hh
  have hgap : b-a ≤ f y-f x := by change f x ≤ a at hx; change b ≤ f y at hy; linarith
  have ht := hgap.trans (le_abs_self (f y-f x))
  nlinarith only [hh, ht]

/-- The two sides of a convex Lipschitz observable are controlled by applying
convex-set separation at two different sublevels. No concavity is required. -/
lemma convex_median_tail_of_separation (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → E) (q : ℝ) (hsep : ConvexSetSeparation μ X q)
    (C : ℝ≥0) (hC : 0 < (C : ℝ)) (f : E → ℝ)
    (hfc : ConvexOn ℝ univ f) (hf : LipschitzWith C f)
    (m δ : ℝ) (hδ : 0 < δ) (hm : IsProbabilityMedian μ (fun x => f (X x)) m) :
    μ.real {x | δ < |f (X x)-m|} ≤ 4*Real.exp (-q*(δ/(C : ℝ))^2) := by
  have hu := convex_sublevel_separation_bound μ X q hsep C hC f hfc hf m (m+δ) (by linarith)
  have hl := convex_sublevel_separation_bound μ X q hsep C hC f hfc hf (m-δ) m (by linarith)
  have eu : m+δ-m=δ := by ring
  have el : m-(m-δ)=δ := by ring
  rw [eu] at hu
  rw [el] at hl
  have hpU := mul_le_mul_of_nonneg_right hm.1 (measureReal_nonneg (μ := μ) (s := {x | m+δ ≤ f (X x)}))
  have hpL := mul_le_mul_of_nonneg_left hm.2 (measureReal_nonneg (μ := μ) (s := {x | f (X x) ≤ m-δ}))
  have hU : μ.real {x | m+δ ≤ f (X x)} ≤ 2*Real.exp (-q*(δ/(C : ℝ))^2) := by linarith
  have hL : μ.real {x | f (X x) ≤ m-δ} ≤ 2*Real.exp (-q*(δ/(C : ℝ))^2) := by linarith
  have hsub : {x | δ < |f (X x)-m|} ⊆
      {x | f (X x) ≤ m-δ} ∪ {x | m+δ ≤ f (X x)} := by
    intro x hx
    by_cases hlx : f (X x) ≤ m-δ
    · exact Or.inl hlx
    · right
      change m+δ ≤ f (X x)
      by_contra hux
      have hb : |f (X x)-m| ≤ δ := abs_le.mpr ⟨by linarith, by linarith⟩
      exact (not_lt_of_ge hb) hx
  have hh := (measureReal_mono (μ := μ) hsub (measure_ne_top _ _)).trans (measureReal_union_le _ _)
  linarith

#print axioms convex_sublevel_separation_bound
#print axioms convex_median_tail_of_separation
end SpectralRadiusUpperTail

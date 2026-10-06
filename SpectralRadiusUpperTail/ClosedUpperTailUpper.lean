import SpectralRadiusUpperTail.Rate
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Topology.Order.Monotone
import Mathlib.Order.Filter.AtTopBot.Basic

namespace SpectralRadiusUpperTail
open MeasureTheory Filter Set

lemma rate_infimum_on_closed_upper_set (β : ℝ) (hβ : 0 < β)
    (F : Set ℝ) (hF : IsClosed F) (hne : F.Nonempty) (h1 : ∀ r ∈ F, 1 < r) :
    1 < sInf F ∧ sInf F ∈ F ∧ sInf (rate β '' F) = rate β (sInf F) := by
  have hbb : BddBelow F := ⟨1, fun r hr => (h1 r hr).le⟩
  have hmem : sInf F ∈ F := hF.csInf_mem hne hbb
  refine ⟨h1 _ hmem, hmem, ?_⟩
  apply IsLeast.csInf_eq
  refine ⟨⟨sInf F, hmem, rfl⟩, ?_⟩
  rintro _ ⟨r, hr, rfl⟩
  rcases (csInf_le hbb hr).eq_or_lt with he | hl
  · rw [he]
  · exact (rate_strict_mono β (sInf F) r hβ (h1 _ hmem).le hl).le

/-- Closed-set LDP upper bounds on sets wholly above one follow directly
from the sharp closed tail. Empty sets are deliberately handled separately. -/
lemma closed_set_exponential_upper_above_one
    (Ω : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)]
    (μ : (n : ℕ) → Measure (Ω n)) [∀ n, IsFiniteMeasure (μ n)]
    (X : (n : ℕ) → Ω n → ℝ) (β : ℝ) (hβ : 0 < β)
    (hupper : ∀ r : ℝ, 1 < r → ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      (μ n).real {x | r ≤ X n x} ≤ Real.exp ((n : ℝ)*(-rate β r+ε)))
    (F : Set ℝ) (hF : IsClosed F) (hne : F.Nonempty) (h1 : ∀ r ∈ F, 1 < r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (μ n).real {ω | X n ω ∈ F} ≤
      Real.exp ((n : ℝ)*(-sInf (rate β '' F)+ε)) := by
  obtain ⟨hr, hmem, hrate⟩ := rate_infimum_on_closed_upper_set β hβ F hF hne h1
  have hbb : BddBelow F := ⟨1, fun r hr => (h1 r hr).le⟩
  filter_upwards [hupper (sInf F) hr ε hε] with n hn
  rw [hrate]
  apply (measureReal_mono (μ := μ n) ?_ (measure_ne_top _ _)).trans hn
  intro ω hω
  exact csInf_le hbb hω

#print axioms rate_infimum_on_closed_upper_set
#print axioms closed_set_exponential_upper_above_one
end SpectralRadiusUpperTail

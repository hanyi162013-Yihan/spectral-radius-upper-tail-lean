import SpectralRadiusUpperTail.ResolventQuantitative
import SpectralRadiusUpperTail.NormProbabilitySum

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology

/-- Uniform resolvent control transfers across an o_P(1) perturbation on the same space.
The baseline resolvent hypothesis is explicit; this lemma does not assert an iid exterior estimate. -/
lemma resolvent_probability_stability
    {𝕂 : Type*} [CommRing 𝕂] (Ω R : ℕ → Type*)
    [∀ n, MeasurableSpace (Ω n)] [∀ n, NormedRing (R n)]
    [∀ n, CompleteSpace (R n)] [∀ n, Algebra 𝕂 (R n)]
    (μ : (n : ℕ) → Measure (Ω n)) [∀ n, IsFiniteMeasure (μ n)]
    (A E : (n : ℕ) → Ω n → R n) (S : Set 𝕂) (M : ℝ) (hM : 0 < M)
    (hbase : Tendsto (fun n => (μ n).real
      {x | ¬ ∀ z ∈ S, z ∈ resolventSet 𝕂 (A n x) ∧ ‖resolvent (A n x) z‖ ≤ M})
      atTop (𝓝 0))
    (herr : ∀ ε : ℝ, 0 < ε → Tendsto (fun n => (μ n).real {x | ε ≤ ‖E n x‖}) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => (μ n).real
      {x | ¬ ∀ z ∈ S, z ∈ resolventSet 𝕂 (A n x+E n x) ∧
        ‖resolvent (A n x+E n x) z‖ ≤ 2*M ∧
        ‖resolvent (A n x+E n x) z-resolvent (A n x) z‖ < ε}) atTop (𝓝 0) := by
  classical
  let δ := min (1/(2*M)) (ε/(4*M^2))
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hlim := hbase.add (herr δ hδ)
  simp only [zero_add] at hlim
  apply squeeze_zero (fun _ => measureReal_nonneg) ?_ hlim
  intro n
  apply le_trans (measureReal_mono ?_) (measureReal_union_le _ _)
  intro x hx
  change (¬ ∀ z ∈ S, z ∈ resolventSet 𝕂 (A n x) ∧ ‖resolvent (A n x) z‖ ≤ M) ∨ δ ≤ ‖E n x‖
  by_cases hb : ∀ z ∈ S, z ∈ resolventSet 𝕂 (A n x) ∧ ‖resolvent (A n x) z‖ ≤ M
  · right
    by_contra he
    have he' : ‖E n x‖ < δ := lt_of_not_ge he
    have h1 := lt_of_lt_of_le he' (min_le_left (1/(2*M)) (ε/(4*M^2)))
    have h2 := lt_of_lt_of_le he' (min_le_right (1/(2*M)) (ε/(4*M^2)))
    have h1' := (lt_div_iff₀ (by positivity : 0 < 2*M)).mp h1
    have h2' := (lt_div_iff₀ (by positivity : 0 < 4*M^2)).mp h2
    apply hx
    intro z hz
    have hh := resolvent_add_quantitative (A n x) (E n x) z M hM.le
      (hb z hz).1 (hb z hz).2 (by nlinarith)
    exact ⟨hh.1, hh.2.1, by nlinarith [hh.2.2]⟩
  · exact Or.inl hb

#print axioms resolvent_probability_stability
end SpectralRadiusUpperTail

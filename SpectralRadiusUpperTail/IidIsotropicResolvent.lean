import SpectralRadiusUpperTail.IidExteriorResolvent
import SpectralRadiusUpperTail.IidCoefficientPower
import SpectralRadiusUpperTail.IsotropicGoodEvent
import SpectralRadiusUpperTail.ResolventTailChoice
import SpectralRadiusUpperTail.FiniteUnionProbabilityLimit

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology BigOperators

/-- Uniform exterior isotropic convergence for prescribed deterministic vectors.
It is not a simultaneous assertion over data-selected directions. -/
lemma iid_isotropic_resolvent_probability (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun z : ℂ => Real.exp (c*‖z‖^2)) μ)
    (hm : (∫ z : ℂ, z ∂μ) = 0) (hv : (∫ z : ℂ, ‖z‖^2 ∂μ) = 1)
    (p q : (n : ℕ) → Fin n → ℂ)
    (hp : ∀ n, (∑ i, ‖p n i‖^2) ≤ 1) (hq : ∀ n, (∑ i, ‖q n i‖^2) ≤ 1)
    (r ε : ℝ) (hr : 1 < r) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (Measure.pi (fun _ : Fin n × Fin n => μ)).real
      {x | ¬ matrixIsotropicControl (normalizedIidMatrix x) (p n) (q n) r ε})
      atTop (𝓝 0) := by
  obtain ⟨C,hC,hbase⟩ := iid_exterior_resolvent_probability μ c hc hexp hm hv r hr
  obtain ⟨k,htail⟩ := exists_small_resolvent_tail r C ε hr hε
  let δ := ε/(4*(k+1 : ℝ))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let law := fun n => Measure.pi (fun _ : Fin n × Fin n => μ)
  let E0 := fun n => {x : Fin n × Fin n → ℂ | ¬ matrixExteriorControl (normalizedIidMatrix x) r C}
  let E1 := fun n => {x : Fin n × Fin n → ℂ | (k+3 : ℝ) ≤
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) ((normalizedIidMatrix x)^(k+1))‖}
  let E2 := fun j n => {x : Fin n × Fin n → ℂ | δ ≤
    ‖matrixCoefficient (p n) (q n) ((normalizedIidMatrix x)^(j+1))‖}
  have hpower : Tendsto (fun n => (law n).real (E1 n)) atTop (𝓝 0) := by
    exact normalizedPower_operator_probability_tendsto μ c hc hexp hm hv (k+1) (k+3)
      (by push_cast; linarith)
  have hfinite : Tendsto (fun n => (law n).real (⋃ j ∈ Finset.range k, E2 j n)) atTop (𝓝 0) :=
    finite_union_probability_tendsto (Finset.range k) (fun n => Fin n × Fin n → ℂ) law E2
      (fun j _ => iidCoefficient_power_probability_tendsto μ c hc hexp hm (j+1)
        (by omega) p q hp hq δ hδ)
  have ht := (hbase.add hpower).add hfinite
  simp only [zero_add] at ht
  apply squeeze_zero (fun _ => measureReal_nonneg) _ ht
  intro n
  have hs : {x | ¬ matrixIsotropicControl (normalizedIidMatrix x) (p n) (q n) r ε} ⊆
      (E0 n ∪ E1 n) ∪ (⋃ j ∈ Finset.range k, E2 j n) := by
    intro x hx
    by_contra hnot
    have h01 : x ∉ E0 n ∪ E1 n := fun h => hnot (Or.inl h)
    have h2 : x ∉ ⋃ j ∈ Finset.range k, E2 j n := fun h => hnot (Or.inr h)
    have hb : matrixExteriorControl (normalizedIidMatrix x) r C := by
      by_contra hb
      exact h01 (Or.inl hb)
    have hpw : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)
        ((normalizedIidMatrix x)^(k+1))‖ ≤ (k+3 : ℝ) := by
      by_contra hh
      exact h01 (Or.inr (le_of_lt (lt_of_not_ge hh)))
    have hco : ∀ j ∈ Finset.range k,
        ‖matrixCoefficient (p n) (q n) ((normalizedIidMatrix x)^(j+1))‖ ≤ δ := by
      intro j hj
      by_contra hh
      apply h2
      exact Set.mem_iUnion.mpr ⟨j,Set.mem_iUnion.mpr ⟨hj,le_of_lt (lt_of_not_ge hh)⟩⟩
    exact hx (matrixIsotropicControl_of_finite (normalizedIidMatrix x) (p n) (q n)
      (hp n) (hq n) r C ε hr.le hε k htail hb hpw hco)
  apply (measureReal_mono (μ := law n) hs).trans
  apply (measureReal_union_le _ _).trans
  exact add_le_add (measureReal_union_le (E0 n) (E1 n)) (le_refl _)

#print axioms iid_isotropic_resolvent_probability
end SpectralRadiusUpperTail

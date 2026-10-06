import SpectralRadiusUpperTail.FiniteIsotropicFamily
import SpectralRadiusUpperTail.BoundedFamilyPadding

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology BigOperators

/-- The family size can vary with n, provided it has a fixed finite bound. -/
lemma iid_bounded_isotropic_probability (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun z : ℂ => Real.exp (c*‖z‖^2)) μ)
    (hm : (∫ z : ℂ, z ∂μ) = 0) (hv : (∫ z : ℂ, ‖z‖^2 ∂μ) = 1)
    (ι : ℕ → Type*) [∀ n, Fintype (ι n)] (m : ℕ) (hcard : ∀ n, Fintype.card (ι n) ≤ m)
    (p q : (n : ℕ) → ι n → Fin n → ℂ)
    (hp : ∀ n a, (∑ i, ‖p n a i‖^2) ≤ 1)
    (hq : ∀ n a, (∑ i, ‖q n a i‖^2) ≤ 1)
    (r ε : ℝ) (hr : 1 < r) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (Measure.pi (fun _ : Fin n × Fin n => μ)).real
      {x | ∃ a, ¬ matrixIsotropicControl (normalizedIidMatrix x) (p n a) (q n a) r ε})
      atTop (𝓝 0) := by
  let e := fun n => boundedFamilyEmbedding m (hcard n)
  let pp := fun j n => padFiniteFamily (e n) (p n) (fun _ => 0) j
  let qq := fun j n => padFiniteFamily (e n) (q n) (fun _ => 0) j
  have hpp : ∀ j n, (∑ i, ‖pp j n i‖^2) ≤ 1 := by
    intro j n
    exact padFiniteFamily_property (e n) (p n) (fun _ => 0)
      (fun v => (∑ i, ‖v i‖^2) ≤ 1) (hp n) (by simp) j
  have hqq : ∀ j n, (∑ i, ‖qq j n i‖^2) ≤ 1 := by
    intro j n
    exact padFiniteFamily_property (e n) (q n) (fun _ => 0)
      (fun v => (∑ i, ‖v i‖^2) ≤ 1) (hq n) (by simp) j
  have ht := iid_finite_isotropic_probability μ c hc hexp hm hv pp qq hpp hqq r ε hr hε
  apply squeeze_zero (fun _ => measureReal_nonneg) _ ht
  intro n
  apply measureReal_mono (μ := Measure.pi (fun _ : Fin n × Fin n => μ))
  rintro x ⟨a,ha⟩
  refine ⟨e n a,?_⟩
  simpa only [pp,qq,padFiniteFamily_apply] using ha

#print axioms iid_bounded_isotropic_probability
end SpectralRadiusUpperTail

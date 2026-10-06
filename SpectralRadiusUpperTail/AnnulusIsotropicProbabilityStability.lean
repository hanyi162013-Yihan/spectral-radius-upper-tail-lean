import SpectralRadiusUpperTail.FiniteRightIsotropicProbability
import SpectralRadiusUpperTail.MatrixCoefficientDifference
import SpectralRadiusUpperTail.AnnulusProbabilityStability

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology BigOperators Matrix.Norms.L2Operator

lemma annulus_isotropic_probability_stability (Ω : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)]
    (μ : (n : ℕ) → Measure (Ω n)) [∀ n, IsFiniteMeasure (μ n)]
    (A E : (n : ℕ) → Ω n → Matrix (Fin n) (Fin n) ℂ)
    (p q : (n : ℕ) → Fin n → ℂ)
    (hp : ∀ n, (∑ i, ‖p n i‖^2) ≤ 1) (hq : ∀ n, (∑ i, ‖q n i‖^2) ≤ 1)
    (r L C : ℝ) (hC : 0 < C)
    (hbase : Tendsto (fun n => (μ n).real {x | ¬ matrixAnnulusControl (A n x) r L C}) atTop (𝓝 0))
    (hiso : ∀ ε : ℝ, 0 < ε → Tendsto (fun n => (μ n).real
      {x | ¬ matrixAnnulusIsotropicControl (A n x) (p n) (q n) r L ε}) atTop (𝓝 0))
    (herr : ∀ δ : ℝ, 0 < δ → Tendsto (fun n => (μ n).real
      {x | δ ≤ ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (E n x)‖}) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => (μ n).real
      {x | ¬ matrixAnnulusIsotropicControl (A n x+E n x) (p n) (q n) r L ε}) atTop (𝓝 0) := by
  have hstab := annulus_probability_stability Ω μ A E r L C hC hbase herr
    (ε/2) (by positivity)
  have ht := hstab.add (hiso (ε/2) (by positivity))
  simp only [zero_add] at ht
  apply squeeze_zero (fun _ => measureReal_nonneg) _ ht
  intro n
  apply le_trans (measureReal_mono (μ := μ n) ?_) (measureReal_union_le _ _)
  intro x hx
  by_contra hb
  have hg : ∀ z : ℂ, r ≤ ‖z‖ → ‖z‖ ≤ L → z ∈ resolventSet ℂ (A n x+E n x) ∧
      ‖resolvent (A n x+E n x) z‖ ≤ 2*C ∧
      ‖resolvent (A n x+E n x) z-resolvent (A n x) z‖ < ε/2 := by
    by_contra hg
    exact hb (Or.inl hg)
  have ho : matrixAnnulusIsotropicControl (A n x) (p n) (q n) r L (ε/2) := by
    by_contra ho
    exact hb (Or.inr ho)
  apply hx
  intro z hz hzL
  refine ⟨(hg z hz hzL).1,?_⟩
  have hd := (matrixCoefficient_difference_le (p n) (q n) (hp n) (hq n)
    (resolvent (A n x+E n x) z) (resolvent (A n x) z)).trans_lt (hg z hz hzL).2.2
  have he := (ho z hz hzL).2
  have ht := norm_add_le
    (matrixCoefficient (p n) (q n) (resolvent (A n x+E n x) z)-
      matrixCoefficient (p n) (q n) (resolvent (A n x) z))
    (matrixCoefficient (p n) (q n) (resolvent (A n x) z)-z⁻¹*matrixCoefficient (p n) (q n) 1)
  rw [sub_add_sub_cancel] at ht
  linarith

#print axioms annulus_isotropic_probability_stability
end SpectralRadiusUpperTail

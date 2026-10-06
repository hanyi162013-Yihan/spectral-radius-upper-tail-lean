import SpectralRadiusUpperTail.EvenMomentSquareExp
import SpectralRadiusUpperTail.RealMatchingFromCutoffConcentration

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology

/-- Only positive even moments need to be supplied for a probability law. -/
lemma gaussian_even_domination_of_positive (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h : ∀ m : ℕ, 0 < m → Integrable (fun x : ℝ => x^(2*m)) μ ∧
      (∫ x : ℝ, x^(2*m) ∂μ) ≤ ∫ x : ℝ, x^(2*m) ∂standardNormal) :
    GaussianEvenMomentDomination μ := by
  intro m
  by_cases hm : m = 0
  · subst m
    simp
  · exact h m (Nat.pos_of_ne_zero hm)

/-- The manuscript's real matching class supplies all entry assumptions of
the already proved lower-bound application. Concentration remains explicit;
no real sharp upper bound is asserted here. -/
theorem real_class_matching_lower (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hsym : μ.map (fun x : ℝ => -x) = μ)
    (hvar : (∫ x : ℝ, x^2 ∂μ) = 1)
    (h : GaussianEvenMomentDomination μ)
    (r : ℝ) (hr : 1 < r) (hcut : CutoffConvexConcentration μ)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, Real.exp ((n : ℝ)*(-rate 1 r-ε)) ≤
      (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).real
        {x | r < (spectralRadius ℂ ((normalizedArray x).map Complex.ofRealHom)).toReal} := by
  have hm : (∫ x : ℝ, x ∂μ) = 0 := by
    simpa using symmetric_real_odd_moment μ hsym 0
  have hv : (∫ x : ℝ, ‖x‖^2 ∂μ) = 1 := by
    simpa only [Real.norm_eq_abs, sq_abs] using hvar
  have he : Integrable (fun x : ℝ => Real.exp (4*(1/16)*‖x‖^2)) μ := by
    convert (dominated_even_squareExp μ h).1 using 1
    funext x
    congr 1
    rw [Real.norm_eq_abs, sq_abs]
    ring
  exact real_matching_exponential_lower_of_cutoff_concentration μ hm hv (1/16)
    (by norm_num) he r hr hcut ε hε

lemma sign_gaussian_even_domination : GaussianEvenMomentDomination signMeasure := by
  intro m
  exact ⟨sign_integrable _, sign_moment_le_standardNormal _⟩

lemma standardNormal_gaussian_even_domination : GaussianEvenMomentDomination standardNormal := by
  intro m
  exact ⟨standardNormal_pow_integrable _, le_rfl⟩

#print axioms gaussian_even_domination_of_positive
#print axioms real_class_matching_lower
#print axioms sign_gaussian_even_domination
#print axioms standardNormal_gaussian_even_domination
end SpectralRadiusUpperTail

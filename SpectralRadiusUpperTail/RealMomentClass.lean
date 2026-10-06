import SpectralRadiusUpperTail.MatrixMoments

namespace SpectralRadiusUpperTail
open MeasureTheory

/-- Finiteness is included in Gaussian even-moment domination. Symmetry and
unit variance are kept separate, matching the manuscript's hypotheses. -/
def GaussianEvenMomentDomination (μ : Measure ℝ) : Prop :=
  ∀ m : ℕ, Integrable (fun x : ℝ => x^(2*m)) μ ∧
    (∫ x : ℝ, x^(2*m) ∂μ) ≤ ∫ x : ℝ, x^(2*m) ∂standardNormal

lemma dominated_even_all_powers_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h : GaussianEvenMomentDomination μ) (k : ℕ) :
    Integrable (fun x : ℝ => x^k) μ := by
  apply ((integrable_const (1 : ℝ)).add (h k).1).mono' (by fun_prop)
  filter_upwards [] with x
  have he : x^(2*k) = (x^k)^2 := by ring
  change |x^k| ≤ 1+x^(2*k)
  rw [he]
  nlinarith [sq_nonneg (|x^k|-1), sq_abs (x^k)]

lemma symmetric_real_odd_moment (μ : Measure ℝ)
    (hsym : μ.map (fun x : ℝ => -x) = μ) (m : ℕ) :
    (∫ x : ℝ, x^(2*m+1) ∂μ) = 0 := by
  have he : (∫ x : ℝ, x^(2*m+1) ∂μ) =
      -(∫ x : ℝ, x^(2*m+1) ∂μ) := by
    calc
      _ = ∫ x : ℝ, x^(2*m+1) ∂μ.map (fun x : ℝ => -x) := by rw [hsym]
      _ = ∫ x : ℝ, (-x)^(2*m+1) ∂μ := integral_map (by fun_prop) (by fun_prop)
      _ = _ := by simp [pow_add, pow_mul, integral_neg]
  linarith

lemma symmetric_dominated_moments (μ : Measure ℝ)
    (hsym : μ.map (fun x : ℝ => -x) = μ)
    (h : GaussianEvenMomentDomination μ) (k : ℕ) :
    0 ≤ (∫ x : ℝ, x^k ∂μ) ∧
      (∫ x : ℝ, x^k ∂μ) ≤ ∫ x : ℝ, x^k ∂standardNormal := by
  obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' k
  · rw [hm]
    exact ⟨integral_nonneg (fun x => by rw [pow_mul]; positivity), (h m).2⟩
  · rw [hm, symmetric_real_odd_moment μ hsym, standardNormal_odd_moment]
    exact ⟨le_rfl, le_rfl⟩

/-- Actual iid matrices in the real matching class satisfy Gaussian power
moment comparison, for every dimension and power, including n^(-1/2) scaling. -/
theorem real_class_normalized_power_comparison (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hsym : μ.map (fun x : ℝ => -x) = μ)
    (h : GaussianEvenMomentDomination μ) (n k : ℕ) :
    (∫ x, scaledFrobeniusPowerSquared (1/Real.sqrt n) k x
      ∂Measure.pi (fun _ : Fin n × Fin n => μ)) ≤
    ∫ x, scaledFrobeniusPowerSquared (1/Real.sqrt n) k x ∂gaussianMatrixLaw n := by
  simp_rw [scaledFrobeniusPowerSquared_eq, integral_const_mul]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  exact matrix_power_moment_comparison (fun _ => μ) (fun _ => standardNormal)
    (fun _ => dominated_even_all_powers_integrable μ h)
    (fun _ => standardNormal_pow_integrable)
    (fun _ k => (symmetric_dominated_moments μ hsym h k).1)
    (fun _ k => (symmetric_dominated_moments μ hsym h k).2) k

#print axioms real_class_normalized_power_comparison
#print axioms dominated_even_all_powers_integrable
end SpectralRadiusUpperTail

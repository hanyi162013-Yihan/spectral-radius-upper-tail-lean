import SpectralRadiusUpperTail.SpectralPowerMarkov
import SpectralRadiusUpperTail.MomentExponentTransfer
import SpectralRadiusUpperTail.IidMatrixFlatten
import SpectralRadiusUpperTail.RealSharpClass

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology

/-- Actual normalized real Gaussian Hilbert--Schmidt power moment. -/
noncomputable def gaussianPowerMoment (n k : ℕ) : ℝ :=
  ∫ x, scaledFrobeniusPowerSquared (1/Real.sqrt n) k x ∂gaussianMatrixLaw n

/-- The remaining real Gaussian upper-moment input. This is a hypothesis,
not a proved Gaussian/Schur asymptotic theorem. Only an upper estimate is used. -/
def GaussianPowerUpperInput : Prop :=
  ∀ α : ℝ, 0 < α → ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
    gaussianPowerMoment n ⌊α*(n : ℝ)⌋₊ ≤ Real.exp ((n : ℝ)*(powerRate 1 α+δ))

lemma real_nested_spectral_power_markov (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hsym : μ.map (fun x : ℝ => -x) = μ) (h : GaussianEvenMomentDomination μ)
    (n k : ℕ) (hk : k ≠ 0) (r : ℝ) (hr : 0 < r) :
    (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).real
      {x | r ≤ (spectralRadius ℂ ((normalizedArray x).map Complex.ofRealHom)).toReal} ≤
      gaussianPowerMoment n k/r^(2*k) := by
  have hm := real_class_spectral_power_markov μ hsym h n k hk r hr
  let P := Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))
  let f := fun x : Fin n → Fin n → ℝ => fun ij : Fin n × Fin n => x ij.1 ij.2
  let S : Set (Fin n × Fin n → ℝ) := {x | r ≤ realMatrixRadius ((1/Real.sqrt n) • entryMatrix x)}
  have hf : Measurable f := by fun_prop
  have he := Measure.le_map_apply hf.aemeasurable S (μ := P)
  have hflat : P.map f = Measure.pi (fun _ : Fin n × Fin n => μ) := iid_matrix_flatten_law μ n
  rw [hflat] at he
  have hp := ENNReal.toReal_mono (measure_ne_top _ _) he
  apply le_trans ?_ hm
  exact hp

theorem real_class_sharp_upper_of_gaussian_power (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hsym : μ.map (fun x : ℝ => -x) = μ) (h : GaussianEvenMomentDomination μ)
    (hG : GaussianPowerUpperInput) (r : ℝ) (hr : 1 < r) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).real
        {x | r ≤ (spectralRadius ℂ ((normalizedArray x).map Complex.ofRealHom)).toReal} ≤
      Real.exp ((n : ℝ)*(-rate 1 r+ε)) := by
  apply sharp_tail_of_power_moments _ gaussianPowerMoment 1 r (by norm_num) hr ?_ hG ε hε
  intro α hα
  filter_upwards [floor_linear_power_eventually_pos α hα] with n hn
  exact real_nested_spectral_power_markov μ hsym h n _ hn.ne' r (by linarith)

#print axioms real_nested_spectral_power_markov
#print axioms real_class_sharp_upper_of_gaussian_power
end SpectralRadiusUpperTail

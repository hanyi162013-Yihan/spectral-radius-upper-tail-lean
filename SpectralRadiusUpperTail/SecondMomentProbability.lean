import SpectralRadiusUpperTail.SpectralTail

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology

lemma norm_probability_le_secondMoment {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → E)
    (hi : Integrable (fun x => ‖f x‖^2) μ) (r : ℝ) (hr : 0 < r) :
    μ.real {x | r ≤ ‖f x‖} ≤ (∫ x, ‖f x‖^2 ∂μ)/r^2 := by
  have hsub : {x | r ≤ ‖f x‖} ⊆ {x | r^2 ≤ ‖f x‖^2} := by
    intro x hx
    exact (sq_le_sq₀ hr.le (norm_nonneg _)).mpr hx
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall (fun x => sq_nonneg ‖f x‖)) hi (r^2)
  have hh := (mul_le_mul_of_nonneg_left (measureReal_mono (μ := μ) hsub) (sq_nonneg r)).trans hm
  exact (le_div_iff₀ (sq_pos_of_pos hr)).mpr (by simpa only [mul_comm] using hh)

/-- Second-moment convergence implies norm convergence in probability even
when the sample and normed spaces vary with the index. -/
theorem norm_probability_tendsto_of_secondMoment (Ω E : ℕ → Type*)
    [∀ n, MeasurableSpace (Ω n)] [∀ n, NormedAddCommGroup (E n)]
    (μ : (n : ℕ) → Measure (Ω n)) [∀ n, IsFiniteMeasure (μ n)]
    (f : (n : ℕ) → Ω n → E n)
    (hi : ∀ᶠ n in atTop, Integrable (fun x => ‖f n x‖^2) (μ n))
    (hmean : Tendsto (fun n => ∫ x, ‖f n x‖^2 ∂μ n) atTop (𝓝 0))
    (r : ℝ) (hr : 0 < r) :
    Tendsto (fun n => (μ n).real {x | r ≤ ‖f n x‖}) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg))
    (hi.mono (fun n hin => norm_probability_le_secondMoment (μ n) (f n) hin r hr))
  simpa only [zero_div] using hmean.div_const (r^2)

#print axioms norm_probability_tendsto_of_secondMoment
end SpectralRadiusUpperTail

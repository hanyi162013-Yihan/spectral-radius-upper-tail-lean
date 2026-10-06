import SpectralRadiusUpperTail.Rate

namespace SpectralRadiusUpperTail

noncomputable def complexRegularizedRate (u b : ℝ) : ℝ :=
  b^2/(1+u)-1-2*Real.log b+Real.log (1+u)

noncomputable def complexAnnealedExponent (u b : ℝ) : ℝ :=
  Real.log (u/(1+u))-b^2/(1+u)

lemma complexRegularizedRate_annulus_lower (u r R b : ℝ) (hu : 0 ≤ u)
    (hr : 1 < r) (hrb : r ≤ b) (hbR : b ≤ R) :
    rate 2 r-u*R^2 ≤ complexRegularizedRate u b := by
  have hden : 0 < 1+u := by positivity
  have hb : 0 ≤ b := by linarith
  have hmono : rate 2 r ≤ rate 2 b := by
    rcases lt_or_eq_of_le hrb with hlt | heq
    · exact (rate_strict_mono 2 r b (by norm_num) hr.le hlt).le
    · rw [heq]
  have hdiv : u/(1+u) ≤ u := (div_le_iff₀ hden).mpr (by nlinarith [sq_nonneg u])
  have hprod := mul_le_mul (pow_le_pow_left₀ hb hbR 2) hdiv
    (div_nonneg hu hden.le) (sq_nonneg R)
  have hlog : 0 ≤ Real.log (1+u) := Real.log_nonneg (by linarith)
  have he : rate 2 b-complexRegularizedRate u b = b^2*(u/(1+u))-Real.log (1+u) := by
    unfold rate complexRegularizedRate
    field_simp
    <;> ring
  linarith

lemma complex_witness_rate_cancellation (u b d L : ℝ) (hu : 0 < u) :
    complexAnnealedExponent u b-(Real.log u-1-d/u-L) =
      -complexRegularizedRate u b+d/u+L-2*Real.log b := by
  unfold complexAnnealedExponent complexRegularizedRate
  rw [Real.log_div hu.ne' (by positivity : (1+u : ℝ) ≠ 0)]
  ring

lemma complex_fixed_grid_rate_bound (u r R b M ε : ℝ) (hu : 0 < u)
    (hr : 1 < r) (hrb : r ≤ b) (hbR : b ≤ R) :
    complexAnnealedExponent u b-
      (Real.log u-1-u-(2*Real.log b+2*u*M^2+ε)) ≤
        -rate 2 r+u*(1+R^2+2*M^2)+ε := by
  have hJ := complexRegularizedRate_annulus_lower u r R b hu.le hr hrb hbR
  have he := complex_witness_rate_cancellation u b (u^2) (2*Real.log b+2*u*M^2+ε) hu
  have hs : u^2/u = u := by field_simp
  rw [hs] at he
  linarith

#print axioms complexRegularizedRate
#print axioms complexAnnealedExponent
#print axioms complexRegularizedRate_annulus_lower
#print axioms complex_witness_rate_cancellation
#print axioms complex_fixed_grid_rate_bound
end SpectralRadiusUpperTail

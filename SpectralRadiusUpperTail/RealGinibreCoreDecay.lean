import SpectralRadiusUpperTail.RealGinibreCoreDensity
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

/-- The logarithm lies below its tangent at the starting radius. -/
private lemma log_difference_le_tangent (r x : ℝ) (hr : 0 < r)
    (hrx : r ≤ x) :
    Real.log x - Real.log r ≤ (x-r)/r := by
  have hx : 0 < x := hr.trans_le hrx
  rw [← Real.log_div hx.ne' hr.ne']
  have h := Real.log_le_sub_one_of_pos (div_pos hx hr)
  convert h using 1 <;> field_simp

/-- The real Ginibre density core has a uniform exponential envelope
to the right of every fixed radius strictly above one. -/
theorem realGinibreCoreDensity_log_decay (n : ℕ) (hn : 0 < n)
    (r x : ℝ) (hr : 1 < r) (hrx : r ≤ x) :
    Real.log (realGinibreCoreDensity n x) -
      Real.log (realGinibreCoreDensity n r) ≤
        -(n : ℝ)*(r-1/r)*(x-r) := by
  have hrpos : 0 < r := by linarith
  have hxpos : 0 < x := hrpos.trans_le hrx
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hlog : 0 ≤ Real.log x - Real.log r :=
    sub_nonneg.mpr (Real.log_le_log hrpos hrx)
  have htangent := log_difference_le_tangent r x hrpos hrx
  have h1 :
      Real.log (realGinibreCoreDensity n x)/(n : ℝ) -
        Real.log (realGinibreCoreDensity n r)/(n : ℝ) =
          (1-1/(n : ℝ))*(Real.log x-Real.log r)-
            (x^2-r^2)/2 := by
    rw [realGinibreCoreDensity_log n hn x hxpos,
      realGinibreCoreDensity_log n hn r hrpos]
    unfold realGinibreGammaLogCore
    ring
  have h2 :
      (1-1/(n : ℝ))*(Real.log x-Real.log r)-
          (x^2-r^2)/2 ≤
        (x-r)/r-(x^2-r^2)/2 := by
    have hsmall : (1-1/(n : ℝ))*(Real.log x-Real.log r) ≤
        Real.log x-Real.log r := by
      have hnonneg : 0 ≤ (1/(n : ℝ))*(Real.log x-Real.log r) :=
        mul_nonneg (one_div_nonneg.mpr hnR.le) hlog
      nlinarith
    linarith
  have h3 : (x-r)/r-(x^2-r^2)/2 ≤
      -(r-1/r)*(x-r) := by
    calc
      (x-r)/r-(x^2-r^2)/2 =
          -(r-1/r)*(x-r)-(x-r)^2/2 := by ring
      _ ≤ -(r-1/r)*(x-r) := by nlinarith [sq_nonneg (x-r)]
  have h := h1.trans_le (h2.trans h3)
  have h' :
      (Real.log (realGinibreCoreDensity n x)-
        Real.log (realGinibreCoreDensity n r))/(n : ℝ) ≤
          -(r-1/r)*(x-r) := by convert h using 1 <;> ring
  have h'' := (div_le_iff₀ hnR).mp h'
  calc
    _ ≤ -(r-1/r)*(x-r)*(n : ℝ) := h''
    _ = -(n : ℝ)*(r-1/r)*(x-r) := by ring

/-- Exponentiating the logarithmic estimate gives an integrable right-tail
envelope whose decay rate is explicit. -/
theorem realGinibreCoreDensity_decay (n : ℕ) (hn : 0 < n)
    (r x : ℝ) (hr : 1 < r) (hrx : r ≤ x) :
    realGinibreCoreDensity n x ≤ realGinibreCoreDensity n r *
      Real.exp (-(n : ℝ)*(r-1/r)*(x-r)) := by
  have hrpos : 0 < r := by linarith
  have hxpos : 0 < x := hrpos.trans_le hrx
  have hqx := realGinibreCoreDensity_pos n hn x hxpos
  have hqr := realGinibreCoreDensity_pos n hn r hrpos
  have hlog := realGinibreCoreDensity_log_decay n hn r x hr hrx
  calc
    realGinibreCoreDensity n x =
        Real.exp (Real.log (realGinibreCoreDensity n x)) :=
      (Real.exp_log hqx).symm
    _ ≤ Real.exp (Real.log (realGinibreCoreDensity n r) -
          (n : ℝ)*(r-1/r)*(x-r)) :=
      Real.exp_le_exp.mpr (by linarith)
    _ = realGinibreCoreDensity n r *
          Real.exp (-(n : ℝ)*(r-1/r)*(x-r)) := by
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hqr]
      ring

/-- Above the unit circle the Gamma-normalized real density is decreasing. -/
theorem realGinibreCoreDensity_antitone (n : ℕ) (hn : 0 < n)
    (r x : ℝ) (hr : 1 < r) (hrx : r ≤ x) :
    realGinibreCoreDensity n x ≤ realGinibreCoreDensity n r := by
  have hrpos : 0 < r := by linarith
  have hrr : 0 < r - 1/r := by
    have hs : 1 < r^2 := by nlinarith
    apply sub_pos.mpr
    apply (div_lt_iff₀ hrpos).mpr
    nlinarith
  have harg : -(n : ℝ)*(r-1/r)*(x-r) ≤ 0 := by
    have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have hxr : 0 ≤ x-r := sub_nonneg.mpr hrx
    have hprod := mul_nonneg (mul_nonneg hnR hrr.le) hxr
    nlinarith
  have hexp : Real.exp (-(n : ℝ)*(r-1/r)*(x-r)) ≤ 1 := by
    simpa only [← Real.exp_zero] using Real.exp_le_exp.mpr harg
  have hq := realGinibreCoreDensity_pos n hn r hrpos
  have hm := mul_le_mul_of_nonneg_left hexp hq.le
  exact (realGinibreCoreDensity_decay n hn r x hr hrx).trans (by simpa using hm)

#print axioms realGinibreCoreDensity_log_decay
#print axioms realGinibreCoreDensity_decay
#print axioms realGinibreCoreDensity_antitone
end SpectralRadiusUpperTail

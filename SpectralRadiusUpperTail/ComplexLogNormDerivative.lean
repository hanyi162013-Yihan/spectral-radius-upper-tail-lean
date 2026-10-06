import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

lemma complex_log_norm_hasDerivAt {f : ℝ → ℂ} {d : ℂ} {x : ℝ}
    (hf : HasDerivAt f d x) (hx : f x ≠ 0) :
    HasDerivAt (fun t => Real.log ‖f t‖) (d / f x).re x := by
  have hn : ‖f x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hh := (hf.norm_sq.log (pow_ne_zero 2 hn)).div_const 2
  convert! hh using 1
  · ext t
    rw [Real.log_pow]
    norm_num
  · rw [real_inner_eq_re_inner]
    simp only [RCLike.inner_apply, RCLike.re_eq_complex_re]
    rw [Complex.div_re]
    rw [Complex.normSq_eq_norm_sq]
    simp only [map_mul, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring

#print axioms complex_log_norm_hasDerivAt
end SpectralRadiusUpperTail

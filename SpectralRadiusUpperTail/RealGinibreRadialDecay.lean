import SpectralRadiusUpperTail.RateTwoTailSlope
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

/-- A radial Jacobian costs at most half of the available exterior
Poisson-rate slope. -/
theorem realGinibreRadial_decay (n : ℕ) (r s : ℝ)
    (hr : 1 < r) (hrs : r ≤ s)
    (hn : 1/r ≤ (n : ℝ)*(r-1/r)) :
    s * Real.exp (-(n : ℝ)*rate 2 s) ≤
      r * Real.exp (-(n : ℝ)*rate 2 r) *
        Real.exp (-((n : ℝ)*(r-1/r))*(s-r)) := by
  have hrpos : 0 < r := by linarith
  have hδ : 0 ≤ s-r := sub_nonneg.mpr hrs
  have hlin : s ≤ r * Real.exp ((s-r)/r) := by
    have h := Real.add_one_le_exp ((s-r)/r)
    have hm := mul_le_mul_of_nonneg_left h hrpos.le
    have he : r*(1+(s-r)/r) = s := by field_simp; ring
    nlinarith [hm]
  have hslope := rate_two_tail_slope r s hr hrs
  have hnR : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have harg : (s-r)/r-(n : ℝ)*rate 2 s ≤
      -(n : ℝ)*rate 2 r-((n : ℝ)*(r-1/r))*(s-r) := by
    have hm := mul_le_mul_of_nonneg_left hslope hnR
    have hnr := mul_le_mul_of_nonneg_right hn hδ
    have hdiv : (s-r)/r = (1/r)*(s-r) := by ring
    rw [hdiv]
    nlinarith [hm, hnr]
  have hexp := Real.exp_le_exp.mpr harg
  calc
    s * Real.exp (-(n : ℝ)*rate 2 s) ≤
        (r * Real.exp ((s-r)/r)) * Real.exp (-(n : ℝ)*rate 2 s) :=
      mul_le_mul_of_nonneg_right hlin (Real.exp_pos _).le
    _ = r * Real.exp ((s-r)/r-(n : ℝ)*rate 2 s) := by
      calc
        _ = r * (Real.exp ((s-r)/r) * Real.exp (-(n : ℝ)*rate 2 s)) := by ring
        _ = r * Real.exp ((s-r)/r + -(n : ℝ)*rate 2 s) := by
          rw [Real.exp_add]
        _ = _ := by congr 1; ring
    _ ≤ r * Real.exp (-(n : ℝ)*rate 2 r-
          ((n : ℝ)*(r-1/r))*(s-r)) :=
      mul_le_mul_of_nonneg_left hexp hrpos.le
    _ = _ := by
      calc
        r * Real.exp (-(n : ℝ)*rate 2 r-
          ((n : ℝ)*(r-1/r))*(s-r)) =
          r * Real.exp (-(n : ℝ)*rate 2 r +
            -((n : ℝ)*(r-1/r))*(s-r)) := by congr 1; ring
        _ = r * (Real.exp (-(n : ℝ)*rate 2 r) *
            Real.exp (-((n : ℝ)*(r-1/r))*(s-r))) := by rw [Real.exp_add]
        _ = _ := by ring

#print axioms realGinibreRadial_decay
end SpectralRadiusUpperTail

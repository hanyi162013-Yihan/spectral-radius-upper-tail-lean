import SpectralRadiusUpperTail.RealSchurJacobianPairPair
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

/-- Distinct upper-half-plane conjugate pairs give a nonsingular
four-dimensional real Sylvester operator. -/
theorem realSchur_pair_pair_factor_pos
    (x b c u d e y v : ℝ)
    (hbc : b*c = y^2) (hde : d*e = v^2)
    (hy : 0 < y) (hv : 0 < v)
    (hsep : x ≠ u ∨ y ≠ v) :
    0 < Matrix.det (realSchurPairPairSylvester x b c u d e) := by
  rw [realSchur_pair_pair_factor x b c u d e y v hbc hde]
  apply mul_pos
  · rcases hsep with hx | hyne
    · have hx2 : 0 < (x-u)^2 :=
        sq_pos_of_ne_zero (sub_ne_zero.mpr hx)
      nlinarith [sq_nonneg (y-v)]
    · have hy2 : 0 < (y-v)^2 :=
        sq_pos_of_ne_zero (sub_ne_zero.mpr hyne)
      nlinarith [sq_nonneg (x-u)]
  · have hyvs : 0 < (y+v)^2 :=
      sq_pos_of_ne_zero (ne_of_gt (add_pos hy hv))
    nlinarith [sq_nonneg (x-u)]

#print axioms realSchur_pair_pair_factor_pos
end SpectralRadiusUpperTail

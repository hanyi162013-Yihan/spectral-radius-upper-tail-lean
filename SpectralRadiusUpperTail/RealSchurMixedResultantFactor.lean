import SpectralRadiusUpperTail.RealSchurMixedResultant
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- Characteristic-polynomial data for a real 2×2 block with a
nonreal conjugate pair of roots. -/
noncomputable def realPairCenter (A : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := A.trace/2
noncomputable def realPairHeightSq (A : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  A.det-(realPairCenter A)^2
noncomputable def realPairHeight (A : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  Real.sqrt (realPairHeightSq A)

theorem realPairHeight_sq
    (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : 0 ≤ realPairHeightSq A) :
    (realPairHeight A)^2 = realPairHeightSq A := by
  exact Real.sq_sqrt hA

theorem realPair_trace_eq_two_center
    (A : Matrix (Fin 2) (Fin 2) ℝ) :
    A.trace = 2*realPairCenter A := by
  unfold realPairCenter
  ring

theorem realPair_det_eq_center_sq_add_height_sq
    (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : 0 ≤ realPairHeightSq A) :
    A.det = (realPairCenter A)^2+(realPairHeight A)^2 := by
  rw [realPairHeight_sq A hA]
  unfold realPairHeightSq
  ring

theorem realQuadraticResultant_pair_factor
    (t d u e y v : ℝ)
    (hy : y^2 = d-(t/2)^2)
    (hv : v^2 = e-(u/2)^2) :
    realQuadraticResultant t d u e =
      (((t-u)/2)^2+(y-v)^2)*
        (((t-u)/2)^2+(y+v)^2) := by
  have hd : d=(t/2)^2+y^2 := by linear_combination -hy
  have he : e=(u/2)^2+v^2 := by linear_combination -hv
  rw [hd, he]
  unfold realQuadraticResultant
  ring

/-- The general 2×2 Sylvester determinant has the familiar product of
four complex spectral distances without choosing canonical block entries. -/
theorem realSchurRectangularSylvester_pair_pair_spectral_factor
    (A B : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : 0 ≤ realPairHeightSq A)
    (hB : 0 ≤ realPairHeightSq B) :
    (realSchurRectangularSylvester A B).det =
      ((realPairCenter A-realPairCenter B)^2+
        (realPairHeight A-realPairHeight B)^2)*
      ((realPairCenter A-realPairCenter B)^2+
        (realPairHeight A+realPairHeight B)^2) := by
  rw [realSchurRectangularSylvester_pair_pair_general]
  have h := realQuadraticResultant_pair_factor
    A.trace A.det B.trace B.det (realPairHeight A) (realPairHeight B)
    (realPairHeight_sq A hA) (realPairHeight_sq B hB)
  rw [h]
  rw [realPair_trace_eq_two_center A, realPair_trace_eq_two_center B]
  ring

#print axioms realSchurRectangularSylvester_pair_pair_spectral_factor
end SpectralRadiusUpperTail

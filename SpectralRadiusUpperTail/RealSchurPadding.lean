import SpectralRadiusUpperTail.RealSchurBlockData

namespace SpectralRadiusUpperTail
open scoped Matrix.Norms.Frobenius

/-- A one-dimensional real Schur block embedded in two coordinates uses
this projection as its zeroth power. -/
def realSchurRealProjection : Matrix (Fin 2) (Fin 2) ℝ := !![1,0;0,0]

lemma realSchurDataPower_real_zero (x s : ℝ) :
    realSchurDataPower (.real x) 0 s = realSchurRealProjection := by
  simp [realSchurDataPower, realSchurRealProjection]

lemma realSchurDataPower_pair_zero (x y s : ℝ) :
    realSchurDataPower (.pair x y) 0 s = 1 := by
  simp [realSchurDataPower, schurGapPowerBlock]

lemma realSchurDataPower_real_left_support (x s : ℝ) (k : ℕ) :
    realSchurRealProjection * realSchurDataPower (.real x) k s =
      realSchurDataPower (.real x) k s := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realSchurRealProjection, realSchurDataPower, Matrix.mul_apply, Fin.sum_univ_two]

lemma realSchurDataPower_real_right_support (x s : ℝ) (k : ℕ) :
    realSchurDataPower (.real x) k s * realSchurRealProjection =
      realSchurDataPower (.real x) k s := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realSchurRealProjection, realSchurDataPower, Matrix.mul_apply, Fin.sum_univ_two]

#print axioms realSchurDataPower_real_zero
#print axioms realSchurDataPower_pair_zero
#print axioms realSchurDataPower_real_left_support
#print axioms realSchurDataPower_real_right_support
end SpectralRadiusUpperTail

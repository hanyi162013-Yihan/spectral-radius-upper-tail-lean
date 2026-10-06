import SpectralRadiusUpperTail.HermitianShiftDeterminant
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace SpectralRadiusUpperTail
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {𝕂 : Type*} [RCLike 𝕂] {n : ℕ}

lemma posSemidef_shift_logDet_upper (H : Matrix (Fin n) (Fin n) 𝕂) (hH : H.PosSemidef)
    (s : ℝ) (hs : 0 < s) :
    Real.log ‖(H+(s : 𝕂) • (1 : Matrix (Fin n) (Fin n) 𝕂)).det‖ ≤
      RCLike.re H.trace+(n : ℝ)*s := by
  rw [posSemidef_shift_det_norm H hH s hs.le, Real.log_prod]
  · have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
      Real.log_le_self (add_nonneg (hH.eigenvalues_nonneg i) hs.le))
    have htrace : RCLike.re H.trace = ∑ i, hH.isHermitian.eigenvalues i := by
      rw [hH.isHermitian.trace_eq_sum_eigenvalues, map_sum]
      simp only [RCLike.ofReal_re]
    simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← htrace] using hh
  · intro i _
    exact ne_of_gt (add_pos_of_nonneg_of_pos (hH.eigenvalues_nonneg i) hs)

#print axioms posSemidef_shift_logDet_upper
end SpectralRadiusUpperTail

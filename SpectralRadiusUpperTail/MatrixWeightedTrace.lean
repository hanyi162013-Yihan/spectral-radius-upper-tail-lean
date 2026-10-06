import SpectralRadiusUpperTail.MatrixNormTransport
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic

namespace SpectralRadiusUpperTail
open scoped ComplexOrder Matrix MatrixOrder Matrix.Norms.L2Operator
variable {𝕂 : Type*} [RCLike 𝕂] {ι : Type*} [Fintype ι] [DecidableEq ι]
attribute [local instance] matrixL2RealNormedAlgebra

/-- A PSD weight gives a positive real trace functional even though HU
need not be Hermitian. -/
theorem matrix_weighted_trace_nonneg {H U : Matrix ι ι 𝕂}
    (hH : H.PosSemidef) (hU : U.PosSemidef) : 0 ≤ RCLike.re (H*U).trace := by
  obtain ⟨Q,hQ⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hH.nonneg
  have hp := (hU.mul_mul_conjTranspose_same Q).trace_nonneg
  have he : (H*U).trace = (Q*U*Qᴴ).trace := by
    rw [hQ,Matrix.star_eq_conjTranspose,Matrix.mul_assoc,Matrix.trace_mul_comm]
  rw [he]
  exact (RCLike.nonneg_iff.mp hp).1

theorem matrix_weighted_trace_mono {H U V : Matrix ι ι 𝕂}
    (hH : H.PosSemidef) (hUV : U ≤ V) :
    RCLike.re (H*U).trace ≤ RCLike.re (H*V).trace := by
  have hh := matrix_weighted_trace_nonneg hH (Matrix.le_iff.mp hUV)
  simp only [Matrix.mul_sub,Matrix.trace_sub,map_sub] at hh
  linarith

lemma matrix_exp_posSemidef {H : Matrix ι ι 𝕂} (hH : H.IsHermitian) :
    (NormedSpace.exp H).PosSemidef := by
  have hs : IsSelfAdjoint H := hH
  exact Matrix.nonneg_iff_posSemidef.mp hs.exp_nonneg

#print axioms matrix_weighted_trace_nonneg
#print axioms matrix_weighted_trace_mono
#print axioms matrix_exp_posSemidef
end SpectralRadiusUpperTail

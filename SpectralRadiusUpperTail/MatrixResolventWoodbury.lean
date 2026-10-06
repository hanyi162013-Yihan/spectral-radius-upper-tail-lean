import SpectralRadiusUpperTail.MatrixWoodburyBridge
import SpectralRadiusUpperTail.MatrixNeumannBound
import Mathlib.Algebra.Algebra.Spectrum.Basic

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.L2Operator
variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

lemma matrix_resolvent_woodbury (A : Matrix n n ℂ) (U : Matrix n ι ℂ) (V : Matrix ι n ℂ)
    (z : ℂ) (hz : z ∈ resolventSet ℂ A)
    (hB : IsUnit (1-V*resolvent A z*U)) :
    z ∈ resolventSet ℂ (A+U*V) ∧
      resolvent (A+U*V) z = resolvent A z+
        resolvent A z*U*(1-V*resolvent A z*U)⁻¹*V*resolvent A z := by
  let M := algebraMap ℂ (Matrix n n ℂ) z-A
  have hM : IsUnit M := (spectrum.mem_resolventSet_iff).mp hz
  have hi : M⁻¹ = resolvent A z := Matrix.nonsing_inv_eq_ringInverse M
  have hb : IsUnit (1-V*M⁻¹*U) := by rwa [hi]
  have he : algebraMap ℂ (Matrix n n ℂ) z-(A+U*V) = M-U*V := by dsimp [M]; abel
  refine ⟨(spectrum.mem_resolventSet_iff).mpr ?_,?_⟩
  · rw [he]
    exact matrix_sub_mul_isUnit M U V hM hb
  · change Ring.inverse (algebraMap ℂ (Matrix n n ℂ) z-(A+U*V)) = _
    rw [he,← Matrix.nonsing_inv_eq_ringInverse,matrix_sub_mul_inverse M U V hM hb,hi]

#print axioms matrix_resolvent_woodbury
end SpectralRadiusUpperTail

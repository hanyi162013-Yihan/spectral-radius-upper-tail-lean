import SpectralRadiusUpperTail.HermitianSpectralSums
import SpectralRadiusUpperTail.HermitianDilation
import SpectralRadiusUpperTail.GramRegularizedConvexSplit

namespace SpectralRadiusUpperTail
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder MatrixOrder

lemma hermitian_spectral_sum_square {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (hS : (H*H).IsHermitian) (g : ℝ → ℝ) :
    (∑ i, g (hS.eigenvalues i)) = ∑ i, g ((hH.eigenvalues i)^2) := by
  have he : cfc (fun t : ℝ => t^2) H = H*H := by
    rw [cfc_pow_id H 2 hH.isSelfAdjoint, pow_two]
  have hF : (cfc (fun t : ℝ => t^2) H).IsHermitian := he.symm ▸ hS
  have hh := hermitian_spectral_sum_cfc H hH (fun t => t^2) g hF
  simpa only [he] using hh

lemma hermitianDilation_spectral_sum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (f : ℝ → ℝ) :
    (∑ i, f |(hermitianDilation_isHermitian A).eigenvalues i|) =
      2*(∑ i, f (gramSingularMagnitude A i)) := by
  let H := hermitianDilation A
  let hH := hermitianDilation_isHermitian A
  let G₁ := A*A.conjTranspose
  let G₂ := A.conjTranspose*A
  let hG₁ := Matrix.posSemidef_self_mul_conjTranspose A
  let hG₂ := Matrix.posSemidef_conjTranspose_mul_self A
  have hS : (H*H).IsHermitian := by
    change (hermitianDilation A*hermitianDilation A).IsHermitian
    rw [hermitianDilation_square]
    exact Matrix.IsHermitian.fromBlocks hG₁.isHermitian (by simp) hG₂.isHermitian
  have hh := hermitian_spectral_sum_square H hH hS (fun t => f (Real.sqrt t))
  simp only [Real.sqrt_sq_eq_abs] at hh
  have hb : (Matrix.fromBlocks G₁ 0 0 G₂).IsHermitian :=
    Matrix.IsHermitian.fromBlocks hG₁.isHermitian (by simp) hG₂.isHermitian
  have hblocks := hermitian_spectral_sum_blocks G₁ G₂ hG₁.isHermitian hG₂.isHermitian hb
    (fun t => f (Real.sqrt t))
  have he : H*H = Matrix.fromBlocks G₁ 0 0 G₂ := hermitianDilation_square A
  have hchar : G₁.charpoly = G₂.charpoly := Matrix.charpoly_mul_comm A A.conjTranspose
  have hs := hermitian_spectral_sum_charpoly G₁ G₂ hG₁.isHermitian hG₂.isHermitian hchar
    (fun t => f (Real.sqrt t))
  have hsame : (∑ i, f (Real.sqrt (hS.eigenvalues i))) =
      ∑ i, f (Real.sqrt (hb.eigenvalues i)) :=
    hermitian_spectral_sum_charpoly (H*H) (Matrix.fromBlocks G₁ 0 0 G₂) hS hb
      (congrArg Matrix.charpoly he) (fun t => f (Real.sqrt t))
  rw [hsame, hblocks, hs] at hh
  change _ = 2*(∑ i, f (Real.sqrt (hG₂.isHermitian.eigenvalues i)))
  linarith

#print axioms hermitian_spectral_sum_square
#print axioms hermitianDilation_spectral_sum
end SpectralRadiusUpperTail

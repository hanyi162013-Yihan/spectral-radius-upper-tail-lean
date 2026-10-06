import SpectralRadiusUpperTail.FiniteCoordinateMatrixEmbedding
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.Analysis.Normed.Algebra.Spectrum

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Frobenius ENNReal
open Classical

theorem finiteCoordinateMatrix_charpoly {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : ι ↪ κ) (A : Matrix ι ι ℝ) :
    (finiteCoordinateMatrix e*A*(finiteCoordinateMatrix e)ᵀ).charpoly=
      Polynomial.X^(Fintype.card κ-Fintype.card ι)*A.charpoly := by
  rw [Matrix.charpoly_mul_comm_of_le _ _ (Fintype.card_le_of_injective e e.injective),
    ← Matrix.mul_assoc,finiteCoordinateMatrix_isometry,Matrix.one_mul]

theorem real_matrix_radius_eq_of_zero_padded_charpoly
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ) (d : ℕ)
    (hpoly : B.charpoly=Polynomial.X^d*A.charpoly) :
    spectralRadius ℂ (B.map Complex.ofRealHom)=spectralRadius ℂ (A.map Complex.ofRealHom) := by
  have hchar : (B.map Complex.ofRealHom).charpoly=
      Polynomial.X^d*(A.map Complex.ofRealHom).charpoly := by
    rw [Matrix.charpoly_map,hpoly,Polynomial.map_mul,Polynomial.map_pow,
      Polynomial.map_X,Matrix.charpoly_map]
  have hmem (z : ℂ) : z ∈ spectrum ℂ (B.map Complex.ofRealHom) ↔
      z^d*(A.map Complex.ofRealHom).charpoly.eval z=0 := by
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly,hchar]
    simp only [Polynomial.IsRoot,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_X]
  apply le_antisymm
  · apply iSup₂_le
    intro z hz
    rcases mul_eq_zero.mp ((hmem z).mp hz) with hz0 | hzA
    · have he : z=0 := eq_zero_of_pow_eq_zero hz0
      subst z
      simp only [nnnorm_zero,ENNReal.coe_zero]
      exact zero_le
    · have hm : z ∈ spectrum ℂ (A.map Complex.ofRealHom) :=
        Matrix.mem_spectrum_iff_isRoot_charpoly.mpr hzA
      exact le_iSup_of_le z (le_iSup_of_le hm le_rfl)
  · apply iSup₂_le
    intro z hz
    have hzA := Matrix.mem_spectrum_iff_isRoot_charpoly.mp hz
    have hm : z ∈ spectrum ℂ (B.map Complex.ofRealHom) :=
      (hmem z).mpr (by rw [hzA,mul_zero])
    exact le_iSup_of_le z (le_iSup_of_le hm le_rfl)

theorem finiteCoordinateMatrix_radius {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : ι ↪ κ) (B : Matrix κ κ ℝ)
    (hl : ∀ a b, a ∉ Set.range e → B a b=0)
    (hr : ∀ a b, b ∉ Set.range e → B a b=0) :
    spectralRadius ℂ (B.map Complex.ofRealHom)=
      spectralRadius ℂ ((B.submatrix e e).map Complex.ofRealHom) := by
  apply real_matrix_radius_eq_of_zero_padded_charpoly _ _
    (Fintype.card κ-Fintype.card ι)
  have hh := finiteCoordinateMatrix_charpoly e (B.submatrix e e)
  rw [finiteCoordinateMatrix_reconstruct e B hl hr] at hh
  exact hh

#print axioms finiteCoordinateMatrix_charpoly
#print axioms real_matrix_radius_eq_of_zero_padded_charpoly
#print axioms finiteCoordinateMatrix_radius
end SpectralRadiusUpperTail

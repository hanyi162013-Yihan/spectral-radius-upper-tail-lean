import SpectralRadiusUpperTail.SchurBlockFlatten
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

namespace SpectralRadiusUpperTail
open scoped Matrix BigOperators

lemma flattenSchurBlocks_blockTriangular {N : ℕ}
    (A : Matrix (Fin N) (Fin N) (Matrix (Fin 2) (Fin 2) ℝ))
    (hA : ∀ i j, j < i → A i j = 0) :
    (flattenSchurBlocks A).BlockTriangular Prod.fst := by
  intro a b hba
  change A a.1 b.1 a.2 b.2 = 0
  rw [hA a.1 b.1 hba]
  rfl

private def schurBlockFiberEquiv {N : ℕ} (i : Fin N) :
    {a : Fin N × Fin 2 // a.1 = i} ≃ Fin 2 where
  toFun a := a.1.2
  invFun a := ⟨(i,a),rfl⟩
  left_inv := by
    rintro ⟨⟨j,a⟩,hj⟩
    dsimp at hj
    subst j
    rfl
  right_inv := by intro a; rfl

private lemma flattenSchurBlocks_toSquareBlock {N : ℕ}
    (A : Matrix (Fin N) (Fin N) (Matrix (Fin 2) (Fin 2) ℝ))
    (i : Fin N) :
    Matrix.reindex (schurBlockFiberEquiv i) (schurBlockFiberEquiv i)
      ((flattenSchurBlocks A).toSquareBlock Prod.fst i) = A i i := by
  ext a b
  rfl

/-- The characteristic polynomial of a flattened upper-block-triangular
matrix is the product of the characteristic polynomials of its 2×2 blocks. -/
theorem flattenSchurBlocks_upper_charpoly {N : ℕ}
    (A : Matrix (Fin N) (Fin N) (Matrix (Fin 2) (Fin 2) ℝ))
    (hA : ∀ i j, j < i → A i j = 0) :
    (flattenSchurBlocks A).charpoly = ∏ i : Fin N, (A i i).charpoly := by
  have ht := (flattenSchurBlocks_blockTriangular A hA).charpoly
  have hs : Function.Surjective (fun a : Fin N × Fin 2 => a.1) := by
    intro i
    exact ⟨(i,0),rfl⟩
  rw [Finset.image_univ_of_surjective hs] at ht
  rw [ht]
  apply Finset.prod_congr rfl
  intro i hi
  rw [← flattenSchurBlocks_toSquareBlock A i]
  exact (Matrix.charpoly_reindex (schurBlockFiberEquiv i)
    ((flattenSchurBlocks A).toSquareBlock Prod.fst i)).symm

/-- Every eigenvalue of the flattened triangular matrix comes from one of
its diagonal blocks. -/
private lemma flattenSchurBlocks_upper_complex_charpoly {N : ℕ}
    (A : Matrix (Fin N) (Fin N) (Matrix (Fin 2) (Fin 2) ℝ))
    (hA : ∀ i j, j < i → A i j = 0) :
    ((flattenSchurBlocks A).map Complex.ofRealHom).charpoly =
        ∏ i : Fin N, ((A i i).map Complex.ofRealHom).charpoly := by
    rw [Matrix.charpoly_map, flattenSchurBlocks_upper_charpoly A hA,
      Polynomial.map_prod]
    simp_rw [← Matrix.charpoly_map]

theorem flattenSchurBlocks_upper_spectrum {N : ℕ}
    (A : Matrix (Fin N) (Fin N) (Matrix (Fin 2) (Fin 2) ℝ))
    (hA : ∀ i j, j < i → A i j = 0) (z : ℂ)
    (hz : z ∈ spectrum ℂ ((flattenSchurBlocks A).map Complex.ofRealHom)) :
    ∃ i : Fin N, z ∈ spectrum ℂ ((A i i).map Complex.ofRealHom) := by
  have hroot := (Matrix.mem_spectrum_iff_isRoot_charpoly).mp hz
  rw [flattenSchurBlocks_upper_complex_charpoly A hA,
    Polynomial.isRoot_prod] at hroot
  rcases hroot with ⟨i, _, hi⟩
  exact ⟨i, (Matrix.mem_spectrum_iff_isRoot_charpoly).mpr hi⟩

theorem flattenSchurBlocks_upper_spectrum_of_block {N : ℕ}
    (A : Matrix (Fin N) (Fin N) (Matrix (Fin 2) (Fin 2) ℝ))
    (hA : ∀ i j, j < i → A i j = 0) (i : Fin N) (z : ℂ)
    (hz : z ∈ spectrum ℂ ((A i i).map Complex.ofRealHom)) :
    z ∈ spectrum ℂ ((flattenSchurBlocks A).map Complex.ofRealHom) := by
  apply (Matrix.mem_spectrum_iff_isRoot_charpoly).mpr
  rw [flattenSchurBlocks_upper_complex_charpoly A hA,
    Polynomial.isRoot_prod]
  exact ⟨i, Finset.mem_univ _,
    (Matrix.mem_spectrum_iff_isRoot_charpoly).mp hz⟩

theorem realSchurPaddedMatrix_flattened_charpoly {N : ℕ}
    (n : ℕ) (B : Fin N → RealSchurBlockData)
    (z : (Fin N → ℝ) × (SchurEntryIndex N 2 → ℝ)) :
    (flattenSchurBlocks (realSchurPaddedMatrix n B z)).charpoly =
      ∏ i : Fin N, (realSchurDataPower (B i) 1 (z.1 i)).charpoly := by
  rw [flattenSchurBlocks_upper_charpoly]
  · apply Finset.prod_congr rfl
    intro i hi
    simp [realSchurPaddedMatrix]
  · exact realSchurPaddedMatrix_upper n B z

#print axioms flattenSchurBlocks_upper_charpoly
#print axioms flattenSchurBlocks_upper_spectrum
#print axioms flattenSchurBlocks_upper_spectrum_of_block
#print axioms realSchurPaddedMatrix_flattened_charpoly
end SpectralRadiusUpperTail

import SpectralRadiusUpperTail.RectangularIsometryPower

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Frobenius BigOperators
open Classical

noncomputable def finiteCoordinateMatrix {ι κ : Type*} (e : ι ↪ κ) : Matrix κ ι ℝ :=
  fun a i => if a=e i then 1 else 0

theorem finiteCoordinateMatrix_isometry {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : ι ↪ κ) : (finiteCoordinateMatrix e)ᵀ*finiteCoordinateMatrix e=1 := by
  ext i j
  simp [finiteCoordinateMatrix,Matrix.mul_apply,Matrix.transpose_apply,
    Matrix.one_apply,e.injective.eq_iff,eq_comm]

theorem finiteCoordinateMatrix_restrict {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : ι ↪ κ) (B : Matrix κ κ ℝ) :
    (finiteCoordinateMatrix e)ᵀ*B*finiteCoordinateMatrix e=B.submatrix e e := by
  ext i j
  simp [finiteCoordinateMatrix,Matrix.mul_apply,Matrix.transpose_apply,
    Matrix.submatrix_apply,ite_mul,mul_ite]

theorem finiteCoordinateMatrix_projection_left {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : ι ↪ κ) (B : Matrix κ κ ℝ)
    (hB : ∀ a b, a ∉ Set.range e → B a b=0) :
    finiteCoordinateMatrix e*(finiteCoordinateMatrix e)ᵀ*B=B := by
  rw [Matrix.mul_assoc]
  ext a b
  by_cases ha : a ∈ Set.range e
  · obtain ⟨i,rfl⟩ := ha
    simp [finiteCoordinateMatrix,Matrix.mul_apply,Matrix.transpose_apply,
      ite_mul,e.injective.eq_iff]
  · have hne : ∀ i, a ≠ e i := fun i h => ha ⟨i,h.symm⟩
    simp [finiteCoordinateMatrix,Matrix.mul_apply,hne,hB a b ha]

theorem finiteCoordinateMatrix_projection_right {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : ι ↪ κ) (B : Matrix κ κ ℝ)
    (hB : ∀ a b, b ∉ Set.range e → B a b=0) :
    B*(finiteCoordinateMatrix e*(finiteCoordinateMatrix e)ᵀ)=B := by
  have hh := finiteCoordinateMatrix_projection_left e Bᵀ (fun a b ha => hB b a ha)
  have ht := congrArg Matrix.transpose hh
  simpa only [Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.mul_assoc] using ht

theorem finiteCoordinateMatrix_reconstruct {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : ι ↪ κ) (B : Matrix κ κ ℝ)
    (hl : ∀ a b, a ∉ Set.range e → B a b=0)
    (hr : ∀ a b, b ∉ Set.range e → B a b=0) :
    finiteCoordinateMatrix e*(B.submatrix e e)*(finiteCoordinateMatrix e)ᵀ=B := by
  rw [← finiteCoordinateMatrix_restrict e B]
  calc
    _ = (finiteCoordinateMatrix e*(finiteCoordinateMatrix e)ᵀ*B)*
        (finiteCoordinateMatrix e*(finiteCoordinateMatrix e)ᵀ) := by
      simp only [Matrix.mul_assoc]
    _ = B := by rw [finiteCoordinateMatrix_projection_left e B hl,
      finiteCoordinateMatrix_projection_right e B hr]

theorem finiteCoordinateMatrix_power_norm_sq {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : ι ↪ κ) (B : Matrix κ κ ℝ)
    (hl : ∀ a b, a ∉ Set.range e → B a b=0)
    (hr : ∀ a b, b ∉ Set.range e → B a b=0)
    (k : ℕ) (hk : 0 < k) : ‖B^k‖^2=‖(B.submatrix e e)^k‖^2 := by
  have hh := rectangular_isometry_conjugation_power_norm_sq
    (finiteCoordinateMatrix e) (finiteCoordinateMatrix_isometry e) (B.submatrix e e) k hk
  rw [finiteCoordinateMatrix_reconstruct e B hl hr] at hh
  exact hh

#print axioms finiteCoordinateMatrix_isometry
#print axioms finiteCoordinateMatrix_reconstruct
#print axioms finiteCoordinateMatrix_power_norm_sq
end SpectralRadiusUpperTail

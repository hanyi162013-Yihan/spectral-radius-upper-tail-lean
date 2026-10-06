import SpectralRadiusUpperTail.Triangular
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.BigOperators.Fin

namespace SpectralRadiusUpperTail
open scoped BigOperators
open Matrix
variable {𝕂 : Type*} [Field 𝕂] {n : ℕ}

lemma sum_fin_prefix (f : ℕ → 𝕂) (j : Fin n) :
    (∑ i : Fin n, if (i : ℕ) < j then f i else 0) = ∑ k ∈ Finset.range j, f k := by
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => if k < j then f k else 0) n,
    ← Finset.sum_filter]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_range]
  have hj := j.isLt
  omega

def triangularForwardMatrix (n : ℕ) (v u d : ℕ → 𝕂) : Matrix (Fin n) (Fin n) 𝕂 :=
  (1 : Matrix (Fin n) (Fin n) 𝕂) +
    Matrix.of (fun (i j : Fin n) => if i < j then v i * u j / d j else 0)

def triangularInverseMatrix (n : ℕ) (v u d : ℕ → 𝕂) : Matrix (Fin n) (Fin n) 𝕂 :=
  (1 : Matrix (Fin n) (Fin n) 𝕂) -
    Matrix.of (fun (i j : Fin n) => if i < j then v i * u j / d ((i : ℕ)+1) else 0)

theorem vecMul_triangularForwardMatrix (v u d x : ℕ → 𝕂) (j : Fin n) :
    ((fun i : Fin n => x i) ᵥ* triangularForwardMatrix n v u d) j =
      triangularForward v u d x j := by
  rw [triangularForwardMatrix, vecMul_add, vecMul_one]
  change x j + (∑ i : Fin n, x i * (if i < j then v i * u j / d j else 0)) = _
  unfold triangularForward weightedPrefix
  congr 1
  calc
    (∑ i : Fin n, x i * (if i < j then v i * u j / d j else 0)) =
        ∑ i : Fin n, if (i : ℕ) < j then (u j / d j) * (v i * x i) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [Fin.lt_def]
      by_cases h : (i : ℕ) < j
      · simp only [h, if_true]; ring
      · simp only [h, if_false, mul_zero]
    _ = ∑ k ∈ Finset.range j, (u j / d j) * (v k * x k) :=
      sum_fin_prefix (fun k => (u j / d j) * (v k * x k)) j
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem vecMul_triangularInverseMatrix (v u d x : ℕ → 𝕂) (j : Fin n) :
    ((fun i : Fin n => x i) ᵥ* triangularInverseMatrix n v u d) j =
      x j - u j * ∑ k ∈ Finset.range j, v k * x k / d (k+1) := by
  rw [triangularInverseMatrix, vecMul_sub, vecMul_one]
  change x j - (∑ i : Fin n, x i * (if i < j then v i * u j / d (i+1) else 0)) = _
  congr 1
  calc
    (∑ i : Fin n, x i * (if i < j then v i * u j / d (i+1) else 0)) =
        ∑ i : Fin n, if (i : ℕ) < j then u j * (v i * x i / d (i+1)) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [Fin.lt_def]
      by_cases h : (i : ℕ) < j
      · simp only [h, if_true]; ring
      · simp only [h, if_false, mul_zero]
    _ = ∑ k ∈ Finset.range j, u j * (v k * x k / d (k+1)) :=
      sum_fin_prefix (fun k => u j * (v k * x k / d (k+1))) j
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- The finite matrices in the coupling are actual two-sided inverses. -/
theorem triangular_matrices_mul (v u d : ℕ → 𝕂) (hd : ∀ j, d j ≠ 0)
    (hdu : ∀ j, d j-d (j+1)=v j*u j) (n : ℕ) :
    triangularForwardMatrix n v u d * triangularInverseMatrix n v u d = 1 := by
  have hrows (x : ℕ → 𝕂) :
      ((fun i : Fin n => x i) ᵥ* triangularForwardMatrix n v u d) ᵥ*
        triangularInverseMatrix n v u d = fun i : Fin n => x i := by
    have hf : (fun i : Fin n => x i) ᵥ* triangularForwardMatrix n v u d =
        fun i : Fin n => triangularForward v u d x i :=
      funext (vecMul_triangularForwardMatrix v u d x)
    rw [hf]
    funext j
    rw [vecMul_triangularInverseMatrix]
    exact (triangular_inverse v u d x hd hdu j).symm
  apply Matrix.ext_iff_vecMul.mpr
  intro z
  let x : ℕ → 𝕂 := fun k => if h : k < n then z ⟨k,h⟩ else 0
  have hx : (fun i : Fin n => x i) = z := by
    funext i
    simp [x, i.isLt]
  have h := hrows x
  rw [hx, vecMul_vecMul] at h
  simpa only [vecMul_one] using h

theorem triangular_matrices_mul_reverse (v u d : ℕ → 𝕂) (hd : ∀ j, d j ≠ 0)
    (hdu : ∀ j, d j-d (j+1)=v j*u j) (n : ℕ) :
    triangularInverseMatrix n v u d * triangularForwardMatrix n v u d = 1 :=
  mul_eq_one_comm.mp (triangular_matrices_mul v u d hd hdu n)

/-- The actual row vector of conditional mean coefficients after the inverse transform. -/
theorem triangular_mean_vecMul (v u d : ℕ → 𝕂) (hd : ∀ j, d j ≠ 0)
    (hdu : ∀ j, d j-d (j+1)=v j*u j) (n : ℕ) :
    (fun i : Fin n => u i / d i) ᵥ* triangularInverseMatrix n v u d =
      fun i : Fin n => u i / d 0 := by
  funext j
  rw [vecMul_triangularInverseMatrix v u d (fun k => u k / d k) j]
  have hs : (∑ k ∈ Finset.range j, v k * (u k / d k) / d (k+1)) =
      ∑ k ∈ Finset.range j, (v k * u k) / (d k * d (k+1)) := by
    apply Finset.sum_congr rfl
    intro k _
    simp only [div_eq_mul_inv, _root_.mul_inv_rev]
    ring
  rw [hs]
  have h := triangular_mean_coefficient u d (fun k => v k*u k) hd hdu j
  calc
    u j / d j - u j * ∑ k ∈ Finset.range j, (v k*u k)/(d k*d (k+1)) =
        u j * (1/d j - ∑ k ∈ Finset.range j, (v k*u k)/(d k*d (k+1))) := by ring
    _ = u j / d 0 := h

#print axioms triangular_matrices_mul
#print axioms triangular_matrices_mul_reverse
#print axioms triangular_mean_vecMul
end SpectralRadiusUpperTail

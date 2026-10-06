import SpectralRadiusUpperTail.RealSchurNativeBlockData
import SpectralRadiusUpperTail.SchurBlockFlatten

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Frobenius
open Classical

theorem realSchurNativeBlockData_projection (q : ℕ) (hq : q=1 ∨ q=2) (x u g : ℝ) :
    realSchurDataPower (realSchurNativeBlockData q x u) 0 g=
      Matrix.diagonal (fun a : Fin 2 => if a.val < q then (1 : ℝ) else 0) := by
  rcases hq with rfl | rfl
  · ext a b
    fin_cases a <;> fin_cases b <;>
      simp [realSchurNativeBlockData,realSchurDataPower,Matrix.diagonal_apply]
  · simp only [realSchurNativeBlockData,ite_true,realSchurDataPower_pair_zero]
    ext a b
    simp only [Matrix.one_apply,Matrix.diagonal_apply,if_pos a.isLt]

theorem realSchurNativePaddedBridge_entry {m : ℕ}
    (s : Fin m → ℕ) (hs : ∀ i, s i=1 ∨ s i=2) (n : ℕ) (x u : Fin m → ℝ)
    (z : (Fin m → ℝ) × (SchurEntryIndex m 2 → ℝ)) (i j : Fin m) (a b : Fin 2) :
    realSchurPaddedBridge n (fun i => realSchurNativeBlockData (s i) (x i) (u i)) z i j a b=
      (if a.val < s i then (1 : ℝ) else 0)*
        ((1/Real.sqrt n)*z.2 ((i,j),(a,b)))*
          (if b.val < s j then (1 : ℝ) else 0) := by
  unfold realSchurPaddedBridge
  rw [realSchurNativeBlockData_projection (s i) (hs i),
    realSchurNativeBlockData_projection (s j) (hs j)]
  simp only [Matrix.diagonal_mul,Matrix.mul_diagonal,Matrix.smul_apply,Matrix.of_apply,smul_eq_mul]

theorem realSchurNativePadded_inactive_left {m : ℕ}
    (s : Fin m → ℕ) (hs : ∀ i, s i=1 ∨ s i=2) (n : ℕ) (x u : Fin m → ℝ)
    (z : (Fin m → ℝ) × (SchurEntryIndex m 2 → ℝ))
    (a b : Fin m × Fin 2) (ha : s a.1 ≤ a.2.val) :
    flattenSchurBlocks (realSchurPaddedMatrix n
      (fun i => realSchurNativeBlockData (s i) (x i) (u i)) z) a b=0 := by
  have hh := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A a.2 b.2)
    (realSchurPaddedMatrix_left_support n
      (fun i => realSchurNativeBlockData (s i) (x i) (u i)) z a.1 b.1)
  rw [realSchurNativeBlockData_projection (s a.1) (hs a.1)] at hh
  simp only [Matrix.diagonal_mul,if_neg (Nat.not_lt.mpr ha),zero_mul] at hh
  exact hh.symm

theorem realSchurNativePadded_inactive_right {m : ℕ}
    (s : Fin m → ℕ) (hs : ∀ i, s i=1 ∨ s i=2) (n : ℕ) (x u : Fin m → ℝ)
    (z : (Fin m → ℝ) × (SchurEntryIndex m 2 → ℝ))
    (a b : Fin m × Fin 2) (hb : s b.1 ≤ b.2.val) :
    flattenSchurBlocks (realSchurPaddedMatrix n
      (fun i => realSchurNativeBlockData (s i) (x i) (u i)) z) a b=0 := by
  have hh := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A a.2 b.2)
    (realSchurPaddedMatrix_right_support n
      (fun i => realSchurNativeBlockData (s i) (x i) (u i)) z a.1 b.1)
  rw [realSchurNativeBlockData_projection (s b.1) (hs b.1)] at hh
  simp only [Matrix.mul_diagonal,if_neg (Nat.not_lt.mpr hb),mul_zero] at hh
  exact hh.symm

#print axioms realSchurNativeBlockData_projection
#print axioms realSchurNativePaddedBridge_entry
#print axioms realSchurNativePadded_inactive_left
#print axioms realSchurNativePadded_inactive_right
end SpectralRadiusUpperTail

import SpectralRadiusUpperTail.RealSchurNativeProjection
import SpectralRadiusUpperTail.RealSchurNativeUpperLaw

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Frobenius

theorem realSchurCanonicalDiagonal_apply {m : ℕ} (s : Fin m → ℕ)
    (x u g : Fin m → ℝ) (i : Fin m) (a b : Fin (s i)) :
    realSchurCanonicalDiagonal s x u g ⟨(⟨i,a⟩,⟨i,b⟩),rfl⟩=
      realSchurNativeCanonicalEntries (s i) (x i,u i,g i) (a,b) := by
  have hh := congrArg (fun D : (j : Fin m) → (Fin (s j) × Fin (s j)) → ℝ => D i (a,b))
    ((realSchurMixedDiagonalProductEquiv s).apply_symm_apply
      (fun j => realSchurNativeCanonicalEntries (s j) (x j,u j,g j)))
  exact hh

theorem realSchurCanonicalJoin_scale {m : ℕ} (s : Fin m → ℕ)
    (x u g : Fin m → ℝ) (v : RealSchurMixedStrictUpperEntry s → ℝ)
    (c : ℝ) (hc : 0 < c) :
    realSchurMixedUpperEntryJoin s
      (realSchurCanonicalDiagonal s (fun i => x i/Real.sqrt c) (fun i => u i/c) (fun i => g i/c))
      (fun p => v p/Real.sqrt c)=
        (1/Real.sqrt c) • realSchurMixedUpperEntryJoin s (realSchurCanonicalDiagonal s x u g) v := by
  ext ⟨i,a⟩ ⟨j,b⟩
  by_cases hij : i=j
  · subst j
    simp only [realSchurMixedUpperEntryJoin,dif_pos rfl,realSchurCanonicalDiagonal_apply,
      Matrix.smul_apply,smul_eq_mul]
    rw [realSchurNativeCanonicalEntries_scale (s i) (x i) (u i) (g i) c hc]
    simp [div_eq_mul_inv,mul_comm]
  · by_cases hlt : i<j
    · simp [realSchurMixedUpperEntryJoin,hij,hlt,Matrix.smul_apply,div_eq_mul_inv,mul_comm]
    · simp [realSchurMixedUpperEntryJoin,hij,hlt,Matrix.smul_apply]

theorem realSchurNativePadded_restrict {m : ℕ}
    (s : Fin m → ℕ) (hs : ∀ i, s i=1 ∨ s i=2) (hsmall : ∀ i, s i ≤ 2)
    (n : ℕ) (x u : Fin m → ℝ) (hu : ∀ i, s i=2 → 0 ≤ u i)
    (z : (Fin m → ℝ) × (SchurEntryIndex m 2 → ℝ))
    (hg : ∀ i, s i=2 → 0 ≤ z.1 i) :
    (flattenSchurBlocks (realSchurPaddedMatrix n
      (fun i => realSchurNativeBlockData (s i) (x i) (u i)) z)).submatrix
        (realSchurNativeCoordEmbedding s hsmall) (realSchurNativeCoordEmbedding s hsmall)=
      realSchurMixedUpperEntryJoin s (realSchurCanonicalDiagonal s x u z.1)
        (fun p => realSchurNativeUpperSelect s hsmall z.2 p/Real.sqrt n) := by
  ext ⟨i,a⟩ ⟨j,b⟩
  change realSchurPaddedMatrix n _ z i j (Fin.castLE (hsmall i) a) (Fin.castLE (hsmall j) b)=_
  by_cases hij : i=j
  · subst j
    simp only [realSchurPaddedMatrix,Matrix.of_apply,ite_true,
      realSchurMixedUpperEntryJoin,dif_pos rfl,realSchurCanonicalDiagonal_apply]
    exact realSchurNativeBlockData_entries (s i) (hs i) (x i) (u i) (z.1 i)
      (hu i) (hg i) (hsmall i) a b
  · by_cases hlt : i<j
    · simp only [realSchurPaddedMatrix,Matrix.of_apply,if_neg hij,if_pos hlt,
        realSchurMixedUpperEntryJoin,dif_neg hij,dif_pos hlt]
      rw [realSchurNativePaddedBridge_entry s hs]
      simp only [Fin.val_castLE,if_pos a.isLt,if_pos b.isLt,one_mul,mul_one]
      change (1/Real.sqrt n)*z.2 ((i,j),(Fin.castLE (hsmall i) a,Fin.castLE (hsmall j) b))=
        z.2 ((i,j),(Fin.castLE (hsmall i) a,Fin.castLE (hsmall j) b))/Real.sqrt n
      ring
    · simp [realSchurPaddedMatrix,hij,hlt,realSchurMixedUpperEntryJoin]

theorem realSchurNativePadded_power_norm_sq {m : ℕ}
    (s : Fin m → ℕ) (hs : ∀ i, s i=1 ∨ s i=2) (hsmall : ∀ i, s i ≤ 2)
    (n k : ℕ) (hk : 0 < k) (x u : Fin m → ℝ) (hu : ∀ i, s i=2 → 0 ≤ u i)
    (z : (Fin m → ℝ) × (SchurEntryIndex m 2 → ℝ))
    (hg : ∀ i, s i=2 → 0 ≤ z.1 i) :
    ‖(flattenSchurBlocks (realSchurPaddedMatrix n
      (fun i => realSchurNativeBlockData (s i) (x i) (u i)) z))^k‖^2=
      ‖(realSchurMixedUpperEntryJoin s (realSchurCanonicalDiagonal s x u z.1)
        (fun p => realSchurNativeUpperSelect s hsmall z.2 p/Real.sqrt n))^k‖^2 := by
  rw [realSchurNativeCoordEmbedding_power_norm_sq s hsmall _
    (realSchurNativePadded_inactive_left s hs n x u z)
    (realSchurNativePadded_inactive_right s hs n x u z) k hk,
    realSchurNativePadded_restrict s hs hsmall n x u hu z hg]

#print axioms realSchurCanonicalDiagonal_apply
#print axioms realSchurCanonicalJoin_scale
#print axioms realSchurNativePadded_restrict
#print axioms realSchurNativePadded_power_norm_sq
end SpectralRadiusUpperTail

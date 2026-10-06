import SpectralRadiusUpperTail.RealSchurMixedOrbitDiagonal
import SpectralRadiusUpperTail.FiniteCoordinateMatrixEmbedding

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Frobenius

def realSchurNativeCoordEmbedding {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, s i ≤ 2) :
    RealSchurMixedCoord s ↪ (Fin m × Fin 2) where
  toFun p := (p.1,Fin.castLE (hs p.1) p.2)
  inj' := by
    rintro ⟨i,a⟩ ⟨j,b⟩ h
    have hij : i=j := congrArg Prod.fst h
    subst j
    have hab : a=b := Fin.ext (congrArg (fun p : Fin m × Fin 2 => p.2.val) h)
    subst b
    rfl

theorem realSchurNativeCoordEmbedding_range {m : ℕ} (s : Fin m → ℕ)
    (hs : ∀ i, s i ≤ 2) (a : Fin m × Fin 2) :
    a ∈ Set.range (realSchurNativeCoordEmbedding s hs) ↔ a.2.val < s a.1 := by
  constructor
  · rintro ⟨⟨i,b⟩,rfl⟩
    exact b.isLt
  · intro ha
    refine ⟨⟨a.1,⟨a.2.val,ha⟩⟩,?_⟩
    apply Prod.ext
    · rfl
    · exact Fin.ext rfl

theorem realSchurNativeCoordEmbedding_power_norm_sq {m : ℕ} (s : Fin m → ℕ)
    (hs : ∀ i, s i ≤ 2) (B : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (hl : ∀ a b, s a.1 ≤ a.2.val → B a b=0)
    (hr : ∀ a b, s b.1 ≤ b.2.val → B a b=0)
    (k : ℕ) (hk : 0 < k) :
    ‖B^k‖^2=‖(B.submatrix (realSchurNativeCoordEmbedding s hs)
      (realSchurNativeCoordEmbedding s hs))^k‖^2 := by
  classical
  have hl' : ∀ a b, a ∉ Set.range (realSchurNativeCoordEmbedding s hs) → B a b=0 := by
    intro a b ha
    rw [realSchurNativeCoordEmbedding_range] at ha
    exact hl a b (Nat.le_of_not_lt ha)
  have hr' : ∀ a b, b ∉ Set.range (realSchurNativeCoordEmbedding s hs) → B a b=0 := by
    intro a b hb
    rw [realSchurNativeCoordEmbedding_range] at hb
    exact hr a b (Nat.le_of_not_lt hb)
  exact finiteCoordinateMatrix_power_norm_sq (realSchurNativeCoordEmbedding s hs) B hl' hr' k hk

#print axioms realSchurNativeCoordEmbedding_range
#print axioms realSchurNativeCoordEmbedding_power_norm_sq
end SpectralRadiusUpperTail

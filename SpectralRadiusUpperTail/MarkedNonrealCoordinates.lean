import SpectralRadiusUpperTail.RealSchurMixedNativeDiagonal
import SpectralRadiusUpperTail.MarkedRealTwoBlockOrbit

namespace SpectralRadiusUpperTail

/-- A marked conjugate pair and its unrestricted real complement. -/
abbrev markedNonrealBlockSizes (m : ℕ) : Fin 2 → ℕ := ![2,m]

def markedNonrealCoordEquiv (m : ℕ) :
    (Fin 2 ⊕ Fin m) ≃ RealSchurMixedCoord (markedNonrealBlockSizes m) where
  toFun
    | Sum.inl i => ⟨0,i⟩
    | Sum.inr j => ⟨1,j⟩
  invFun
    | ⟨i,j⟩ => Fin.cases (fun j => Sum.inl j)
        (fun i j => Sum.inr (Fin.cast (by fin_cases i; rfl) j)) i j
  left_inv := by
    intro x
    cases x <;> rfl
  right_inv := by
    rintro ⟨i,j⟩
    induction i using Fin.cases with
    | zero => rfl
    | succ i => fin_cases i; rfl

theorem markedNonrealBlockSizes_pos (m : ℕ) (hm : 0 < m) :
    ∀ i, 0 < markedNonrealBlockSizes m i := by
  intro i
  fin_cases i <;> simp [markedNonrealBlockSizes,hm]

theorem markedNonrealCoord_card (m : ℕ) :
    Fintype.card (RealSchurMixedCoord (markedNonrealBlockSizes m)) = m+2 := by
  rw [← Fintype.card_congr (markedNonrealCoordEquiv m)]
  simp [Nat.add_comm]

def markedNonrealFirstBlock (m : ℕ)
    (T : Matrix (RealSchurMixedCoord (markedNonrealBlockSizes m))
      (RealSchurMixedCoord (markedNonrealBlockSizes m)) ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ := fun i j => T ⟨0,i⟩ ⟨0,j⟩

def markedNonrealComplement (m : ℕ)
    (T : Matrix (RealSchurMixedCoord (markedNonrealBlockSizes m))
      (RealSchurMixedCoord (markedNonrealBlockSizes m)) ℝ) :
    Matrix (Fin m) (Fin m) ℝ := fun i j => T ⟨1,i⟩ ⟨1,j⟩

theorem markedNonreal_lower_zero_iff (m : ℕ)
    (T : Matrix (RealSchurMixedCoord (markedNonrealBlockSizes m))
      (RealSchurMixedCoord (markedNonrealBlockSizes m)) ℝ) :
    realSchurMixedLowerProjection (markedNonrealBlockSizes m) T = 0 ↔
      ∀ (i : Fin m) (j : Fin 2), T ⟨1,i⟩ ⟨0,j⟩=0 := by
  constructor
  · intro h i j
    exact congrFun h ⟨markedRealLowerIndex,(i,j)⟩
  · intro h
    funext p
    obtain ⟨p,i,j⟩ := p
    have hp := markedRealLowerIndex_unique p
    subst p
    exact h i j

#print axioms markedNonrealCoordEquiv
#print axioms markedNonrealBlockSizes_pos
#print axioms markedNonrealCoord_card
#print axioms markedNonreal_lower_zero_iff
end SpectralRadiusUpperTail

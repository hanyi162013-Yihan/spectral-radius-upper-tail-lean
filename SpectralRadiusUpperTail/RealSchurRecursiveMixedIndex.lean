import SpectralRadiusUpperTail.RealSchurRecursiveBlockUpper
import SpectralRadiusUpperTail.RealSchurMixedOrbitDiagonal
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

/-- Adding a first block to a mixed coordinate family is the same as
forming the sum of its coordinates with the remaining mixed coordinates. -/
def realSchurMixedCoordConsEquiv {m : ℕ} (k : ℕ) (s : Fin m → ℕ) :
    (Fin k ⊕ RealSchurMixedCoord s) ≃
      RealSchurMixedCoord (Fin.cons k s) where
  toFun
    | Sum.inl j => ⟨0, j⟩
    | Sum.inr ⟨i, j⟩ => ⟨i.succ, j⟩
  invFun
    | ⟨i, j⟩ => Fin.cases (fun j => Sum.inl j)
        (fun i j => Sum.inr ⟨i, j⟩) i j
  left_inv := by
    intro x
    cases x with
    | inl j => rfl
    | inr p =>
        obtain ⟨i, j⟩ := p
        rfl
  right_inv := by
    intro x
    obtain ⟨i, j⟩ := x
    induction i using Fin.cases with
    | zero => rfl
    | succ i => rfl

/-- Block sizes of a list, indexed by its positions. -/
def realSchurListBlockSize : (s : List ℕ) → Fin s.length → ℕ
  | [], i => i.elim0
  | k :: ks, i => Fin.cases k (realSchurListBlockSize ks) i

/-- The recursive and dependent-sum coordinates for the same block list
are equivalent. This is the index bridge needed to compare the global
invariant-flag construction with the local mixed-Schur charts. -/
def realSchurRecursiveMixedIndexEquiv :
    (s : List ℕ) →
      RealSchurRecursiveBlockIndex s ≃
        RealSchurMixedCoord (realSchurListBlockSize s)
  | [] => {
      toFun := fun x => x.elim
      invFun := fun x => x.1.elim0
      left_inv := fun x => x.elim
      right_inv := fun x => x.1.elim0
    }
  | k :: ks =>
      (Equiv.sumCongr (Equiv.refl (Fin k))
        (realSchurRecursiveMixedIndexEquiv ks)).trans
          (realSchurMixedCoordConsEquiv k (realSchurListBlockSize ks))

#print axioms realSchurMixedCoordConsEquiv
#print axioms realSchurRecursiveMixedIndexEquiv
end SpectralRadiusUpperTail

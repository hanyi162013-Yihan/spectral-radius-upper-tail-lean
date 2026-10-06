import SpectralRadiusUpperTail.RealSchurMixedOrbitDiagonal
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- The two-block coordinates for one marked real eigenline and its
orthogonal complement of dimension `m`. -/
abbrev markedRealTwoBlockSizes (m : ℕ) : Fin 2 → ℕ :=
  fun i => if i = 0 then 1 else m

abbrev markedRealLowerIndex : RealSchurLowerIndex 2 :=
  ⟨(1, 0), by decide⟩

def markedRealZeroCoordinate (m : ℕ) :
    Fin (markedRealTwoBlockSizes m markedRealLowerIndex.1.2) :=
  ⟨0, by change 0 < 1; decide⟩

theorem markedRealLowerIndex_unique (p : RealSchurLowerIndex 2) :
    p = markedRealLowerIndex := by
  rcases p with ⟨⟨i,j⟩,h⟩
  change j < i at h
  have hi : i = 1 := by omega
  have hj : j = 0 := by omega
  subst i
  subst j
  rfl

/-- The only angular variables of this chart are the `m` rotations between
the eigenline and its complement. -/
noncomputable def markedRealOrbitEquiv (m : ℕ) :
    Fin m ≃ RealSchurMixedOrbitIndex (markedRealTwoBlockSizes m) := by
  let f : Fin m → RealSchurMixedOrbitIndex (markedRealTwoBlockSizes m) :=
    fun i => ⟨markedRealLowerIndex, (i, markedRealZeroCoordinate m)⟩
  apply Equiv.ofBijective f
  constructor
  · intro i j h
    injection h with _ hh
    exact congrArg Prod.fst hh
  · intro q
    obtain ⟨p,⟨i,j⟩⟩ := q
    have hp := markedRealLowerIndex_unique p
    subst p
    have hsize : markedRealTwoBlockSizes m markedRealLowerIndex.1.2 = 1 := rfl
    have hjlt : j.val < 1 := by simpa only [hsize] using j.isLt
    have hj : j = markedRealZeroCoordinate m := by
      apply Fin.ext
      dsimp [markedRealZeroCoordinate]
      omega
    rw [hj]
    exact ⟨i, rfl⟩

theorem markedRealOrbitEquiv_apply (m : ℕ) (i : Fin m) :
    markedRealOrbitEquiv m i =
      ⟨markedRealLowerIndex, (i, markedRealZeroCoordinate m)⟩ := by
  rfl

#print axioms markedRealLowerIndex_unique
#print axioms markedRealOrbitEquiv
#print axioms markedRealOrbitEquiv_apply
end SpectralRadiusUpperTail

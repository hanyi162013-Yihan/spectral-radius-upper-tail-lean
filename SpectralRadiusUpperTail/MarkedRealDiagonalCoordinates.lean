import SpectralRadiusUpperTail.MarkedRealRankLayerSum
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Classical
open scoped Matrix

/-- The first scalar diagonal entry of the two-block upper matrix. -/
def markedRealScalarDiagonalEntry (m : ℕ) :
    RealSchurMixedDiagonalEntry (markedRealTwoBlockSizes m) :=
  ⟨(markedRealFirstCoordinate m, markedRealFirstCoordinate m), rfl⟩

/-- An entry of the complementary diagonal block. -/
def markedRealComplementDiagonalEntry (m : ℕ) (i j : Fin m) :
    RealSchurMixedDiagonalEntry (markedRealTwoBlockSizes m) :=
  ⟨(⟨1, i⟩, ⟨1, j⟩), rfl⟩

/-- The diagonal-block entries are one scalar and all entries of the
complementary matrix. -/
def markedRealDiagonalEntrySum (m : ℕ) :
    Unit ⊕ (Fin m × Fin m) →
      RealSchurMixedDiagonalEntry (markedRealTwoBlockSizes m)
  | Sum.inl _ => markedRealScalarDiagonalEntry m
  | Sum.inr p => markedRealComplementDiagonalEntry m p.1 p.2

theorem markedRealDiagonalEntrySum_injective (m : ℕ) :
    Function.Injective (markedRealDiagonalEntrySum m) := by
  intro x y h
  cases x with
  | inl a =>
    cases y with
    | inl b => simp
    | inr p =>
      have hx := congrArg (fun q : RealSchurMixedDiagonalEntry
        (markedRealTwoBlockSizes m) => q.1.1.1) h
      norm_num [markedRealDiagonalEntrySum,
        markedRealScalarDiagonalEntry,
        markedRealComplementDiagonalEntry] at hx
  | inr p =>
    cases y with
    | inl b =>
      have hx := congrArg (fun q : RealSchurMixedDiagonalEntry
        (markedRealTwoBlockSizes m) => q.1.1.1) h
      norm_num [markedRealDiagonalEntrySum,
        markedRealScalarDiagonalEntry,
        markedRealComplementDiagonalEntry] at hx
    | inr q =>
      have hp : p = q := by
        rcases p with ⟨i,j⟩
        rcases q with ⟨k,l⟩
        simpa [markedRealDiagonalEntrySum,
          markedRealComplementDiagonalEntry] using h
      exact congrArg Sum.inr hp

theorem markedRealDiagonalEntrySum_surjective (m : ℕ) :
    Function.Surjective (markedRealDiagonalEntrySum m) := by
  intro p
  rcases p with ⟨⟨⟨i,a⟩,⟨j,b⟩⟩,h⟩
  fin_cases i
  · have hj : j = 0 := by simpa using h.symm
    subst j
    change Fin 1 at a b
    have ha : a = markedRealZeroCoordinate m := Subsingleton.elim _ _
    have hb : b = markedRealZeroCoordinate m := Subsingleton.elim _ _
    subst a
    subst b
    exact ⟨Sum.inl (), rfl⟩
  · have hj : j = 1 := by simpa using h.symm
    subst j
    exact ⟨Sum.inr (a,b), rfl⟩

noncomputable def markedRealDiagonalEntryEquiv (m : ℕ) :
    (Unit ⊕ (Fin m × Fin m)) ≃
      RealSchurMixedDiagonalEntry (markedRealTwoBlockSizes m) :=
  Equiv.ofBijective (markedRealDiagonalEntrySum m)
    ⟨markedRealDiagonalEntrySum_injective m,
      markedRealDiagonalEntrySum_surjective m⟩

#print axioms markedRealDiagonalEntryEquiv
end SpectralRadiusUpperTail

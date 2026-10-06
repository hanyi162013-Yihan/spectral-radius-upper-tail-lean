import SpectralRadiusUpperTail.GaussianInjectiveWordOrthogonality
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators

/-- A principal minor and one permutation term in its determinant. -/
abbrev PrincipalPermutation (ι : Type*) :=
  Σ s : Finset ι, Equiv.Perm s

def principalPermutationEdge
    {ι : Type*} (p : PrincipalPermutation ι) (i : p.1) : ι × ι :=
  (i.1, (p.2 i).1)

def principalPermutationWord
    {ι : Type*} [Fintype ι]
    (p : PrincipalPermutation ι) (x : ι × ι → ℝ) : ℝ :=
  ∏ i : p.1, x (principalPermutationEdge p i)

theorem principalPermutationEdge_injective
    {ι : Type*} (p : PrincipalPermutation ι) :
    Function.Injective (principalPermutationEdge p) := by
  intro i j h
  exact Subtype.ext (congrArg Prod.fst h)

/-- The set of matrix entries used by a determinant permutation term
identifies both its principal minor and the permutation itself. -/
theorem principalPermutation_eq_of_edgeRange_eq
    {ι : Type*} [Fintype ι]
    (p q : PrincipalPermutation ι)
    (h : Set.range (principalPermutationEdge p) =
      Set.range (principalPermutationEdge q)) :
    p = q := by
  obtain ⟨s,π⟩ := p
  obtain ⟨t,τ⟩ := q
  have hst : s = t := by
    ext i
    constructor
    · intro hi
      have hm : principalPermutationEdge (⟨s,π⟩ : PrincipalPermutation ι)
          (⟨i,hi⟩ : s) ∈
          Set.range (principalPermutationEdge (⟨t,τ⟩ : PrincipalPermutation ι)) := by
        rw [← h]
        exact ⟨⟨i,hi⟩,rfl⟩
      obtain ⟨j,hj⟩ := hm
      have hji : (j : ι) = i := congrArg Prod.fst hj
      exact hji ▸ j.property
    · intro hi
      have hm : principalPermutationEdge (⟨t,τ⟩ : PrincipalPermutation ι)
          (⟨i,hi⟩ : t) ∈
          Set.range (principalPermutationEdge (⟨s,π⟩ : PrincipalPermutation ι)) := by
        rw [h]
        exact ⟨⟨i,hi⟩,rfl⟩
      obtain ⟨j,hj⟩ := hm
      have hji : (j : ι) = i := congrArg Prod.fst hj
      exact hji ▸ j.property
  subst t
  have hπτ : π = τ := by
    ext i
    have hm : principalPermutationEdge (⟨s,π⟩ : PrincipalPermutation ι) i ∈
        Set.range (principalPermutationEdge (⟨s,τ⟩ : PrincipalPermutation ι)) := by
      rw [← h]
      exact ⟨i,rfl⟩
    obtain ⟨j,hj⟩ := hm
    have hij : j = i := Subtype.ext (congrArg Prod.fst hj)
    subst j
    exact (congrArg Prod.snd hj).symm
  subst τ
  rfl

/-- Different Gaussian determinant monomials are orthogonal, even
when their principal minors have different sizes. -/
theorem gaussian_principalPermutation_words_cross_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p q : PrincipalPermutation ι) (hpq : p ≠ q) :
    (∫ x : ι × ι → ℝ,
      principalPermutationWord p x * principalPermutationWord q x
      ∂Measure.pi (fun _ => standardNormal)) = 0 := by
  exact gaussian_injective_words_cross_zero_of_ranges_ne
    (principalPermutationEdge p) (principalPermutationEdge q)
    (principalPermutationEdge_injective p)
    (principalPermutationEdge_injective q)
    (fun h => hpq (principalPermutation_eq_of_edgeRange_eq p q h))

#print axioms principalPermutation_eq_of_edgeRange_eq
#print axioms gaussian_principalPermutation_words_cross_zero
end SpectralRadiusUpperTail

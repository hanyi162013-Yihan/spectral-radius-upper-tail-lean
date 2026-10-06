import SpectralRadiusUpperTail.MarkedRealAngularProductSource

namespace SpectralRadiusUpperTail
open Polynomial

/-- The rank of a real root among the strictly smaller real roots of a
nonzero polynomial. Complex roots play no role in this ordering. -/
noncomputable def realPolynomialRootRank (p : ℝ[X]) (x : ℝ) : ℕ :=
  Set.ncard {z : ℝ | p.IsRoot z ∧ z < x}

/-- Two roots of one polynomial cannot have the same real-root rank
unless they are the same root. -/
theorem realPolynomialRootRank_injective_on_roots
    (p : ℝ[X]) (hp : p ≠ 0)
    (x y : ℝ) (hx : p.IsRoot x) (hy : p.IsRoot y)
    (hrank : realPolynomialRootRank p x = realPolynomialRootRank p y) :
    x = y := by
  have hfinite : Set.Finite {z : ℝ | p.IsRoot z} :=
    Polynomial.finite_setOfPred_isRoot hp
  by_contra hxy
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  · let sx : Set ℝ := {z | p.IsRoot z ∧ z < x}
    let sy : Set ℝ := {z | p.IsRoot z ∧ z < y}
    have hsub : sx ⊂ sy := by
      apply Set.ssubset_iff_subset_ne.mpr
      constructor
      · intro z hz
        exact ⟨hz.1, hz.2.trans hlt⟩
      · intro heq
        have hmem : x ∈ sy := ⟨hx,hlt⟩
        rw [← heq] at hmem
        exact (lt_irrefl x) hmem.2
    have hsy : sy.Finite := hfinite.subset (by intro z hz; exact hz.1)
    have hltRank := Set.ncard_lt_ncard hsub hsy
    exact (Nat.ne_of_lt hltRank) hrank
  · let sy : Set ℝ := {z | p.IsRoot z ∧ z < y}
    let sx : Set ℝ := {z | p.IsRoot z ∧ z < x}
    have hsub : sy ⊂ sx := by
      apply Set.ssubset_iff_subset_ne.mpr
      constructor
      · intro z hz
        exact ⟨hz.1, hz.2.trans hgt⟩
      · intro heq
        have hmem : y ∈ sx := ⟨hy,hgt⟩
        rw [← heq] at hmem
        exact (lt_irrefl y) hmem.2
    have hsx : sx.Finite := hfinite.subset (by intro z hz; exact hz.1)
    have hltRank := Set.ncard_lt_ncard hsub hsx
    exact (Nat.ne_of_gt hltRank) hrank

#print axioms realPolynomialRootRank_injective_on_roots
end SpectralRadiusUpperTail

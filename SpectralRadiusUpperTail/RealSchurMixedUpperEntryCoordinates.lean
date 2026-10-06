import SpectralRadiusUpperTail.RealSchurMixedGaussianFactorization
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

abbrev RealSchurMixedDiagonalEntry {m : ℕ} (s : Fin m → ℕ) :=
  {p : RealSchurMixedCoord s × RealSchurMixedCoord s // p.1.1 = p.2.1}

abbrev RealSchurMixedStrictUpperEntry {m : ℕ} (s : Fin m → ℕ) :=
  {p : RealSchurMixedCoord s × RealSchurMixedCoord s // p.1.1 < p.2.1}

/-- Assemble independent diagonal-block and strictly-upper-block entries
into a block-upper matrix. -/
def realSchurMixedUpperEntryJoin
    {m : ℕ} (s : Fin m → ℕ)
    (d : RealSchurMixedDiagonalEntry s → ℝ)
    (u : RealSchurMixedStrictUpperEntry s → ℝ) :
    Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ :=
  fun i j => if h : i.1=j.1 then d ⟨(i,j),h⟩
    else if h : i.1<j.1 then u ⟨(i,j),h⟩ else 0

theorem realSchurMixedUpperEntryJoin_lower_zero
    {m : ℕ} (s : Fin m → ℕ)
    (d : RealSchurMixedDiagonalEntry s → ℝ)
    (u : RealSchurMixedStrictUpperEntry s → ℝ) :
    realSchurMixedLowerProjection s
      (realSchurMixedUpperEntryJoin s d u) = 0 := by
  funext p
  change realSchurMixedUpperEntryJoin s d u
    ⟨p.1.1.1,p.2.1⟩ ⟨p.1.1.2,p.2.2⟩ = 0
  simp [realSchurMixedUpperEntryJoin, ne_of_gt p.1.2,
    not_lt_of_ge (le_of_lt p.1.2)]

/-- A block-upper matrix is exactly the independent collection of its
diagonal-block and strictly-upper-block entries. -/
noncomputable def realSchurMixedUpperEntryEquiv
    {m : ℕ} (s : Fin m → ℕ) :
    realSchurMixedUpperSubmodule s ≃ₗ[ℝ]
      ((RealSchurMixedDiagonalEntry s → ℝ) ×
        (RealSchurMixedStrictUpperEntry s → ℝ)) where
  toFun A := (fun p => A.val p.1.1 p.1.2,
    fun p => A.val p.1.1 p.1.2)
  invFun x := ⟨realSchurMixedUpperEntryJoin s x.1 x.2,
    realSchurMixedUpperEntryJoin_lower_zero s x.1 x.2⟩
  left_inv A := by
    apply Subtype.ext
    ext i j
    change realSchurMixedUpperEntryJoin s
      (fun p : RealSchurMixedDiagonalEntry s => A.val p.1.1 p.1.2)
      (fun p : RealSchurMixedStrictUpperEntry s => A.val p.1.1 p.1.2)
        i j = A.val i j
    by_cases hd : i.1=j.1
    · simp [realSchurMixedUpperEntryJoin, hd]
    by_cases hu : i.1 < j.1
    · simp [realSchurMixedUpperEntryJoin, hd, hu]
    have hl : j.1 < i.1 := by omega
    have hz : A.val i j=0 :=
      (realSchurMixed_blockTriangular_iff_lower_zero s A.val).mpr A.property
        (i := i) (j := j) hl
    simp [realSchurMixedUpperEntryJoin, hd, hu, hz]
  right_inv x := by
    apply Prod.ext
    · funext p
      simp [realSchurMixedUpperEntryJoin, p.2]
    · funext p
      simp [realSchurMixedUpperEntryJoin, ne_of_lt p.2, p.2]
  map_add' A B := by
    apply Prod.ext <;> funext p <;> rfl
  map_smul' a A := by
    apply Prod.ext <;> funext p <;> rfl

#print axioms realSchurMixedUpperEntryEquiv
end SpectralRadiusUpperTail

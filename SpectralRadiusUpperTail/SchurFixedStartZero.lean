import SpectralRadiusUpperTail.SchurFixedStartPathSum
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped BigOperators

private instance fixedStartZeroUnique (N : ℕ) (i : Fin N) :
    Unique {p : IncreasingBlockPath N 0 // p.val 0 = i} where
  default := ⟨⟨fun _ => i, by
    intro a b hab
    have heq : a = b := (Fin.eq_zero a).trans (Fin.eq_zero b).symm
    subst b
    exact (lt_irrefl a hab).elim⟩, rfl⟩
  uniq p := by
    apply Subtype.ext
    apply Subtype.ext
    funext a
    have ha : a = (0 : Fin 1) := Fin.eq_zero a
    subst a
    exact p.property

private instance zeroWaitingUnique (k : ℕ) : Unique (SchurWaitingTimes k 0) where
  default := ⟨fun _ => k, by simp⟩
  uniq t := by
    apply Subtype.ext
    funext a
    have ha : a = (0 : Fin 1) := Fin.eq_zero a
    subst a
    simpa using t.property

/-- A path with no upper-triangular edge consists of exactly one diagonal
block and one waiting time, so its contribution is the diagonal power. -/
theorem schurFixedStartPathSum_zero (d N k : ℕ)
    (D : Fin N → Matrix (Fin d) (Fin d) ℝ)
    (U : Matrix (Fin N) (Fin N) (Matrix (Fin d) (Fin d) ℝ))
    (i j : Fin N) :
    schurFixedStartPathSum d N 0 k D U i j =
      if i = j then (D i)^k else 0 := by
  letI := fixedStartZeroUnique N i
  letI := zeroWaitingUnique k
  have hpath : (default : {p : IncreasingBlockPath N 0 // p.val 0 = i}).val.val 0 = i :=
    (default : {p : IncreasingBlockPath N 0 // p.val 0 = i}).property
  have hwait : (default : SchurWaitingTimes k 0).val 0 = k := by
    simpa using (default : SchurWaitingTimes k 0).property
  unfold schurFixedStartPathSum
  rw [Fintype.sum_prod_type, Fintype.sum_unique, Fintype.sum_unique]
  simp [schurStrictPathTerm, gaussianMatrixChain, hpath, hwait]

#print axioms schurFixedStartPathSum_zero
end SpectralRadiusUpperTail

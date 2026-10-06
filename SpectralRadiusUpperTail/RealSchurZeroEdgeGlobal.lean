import SpectralRadiusUpperTail.RealSchurGlobalOrthogonality
import SpectralRadiusUpperTail.SchurFixedStartZero

namespace SpectralRadiusUpperTail
open scoped BigOperators

private instance zeroWaitingUniqueGlobal (k : ℕ) : Unique (SchurWaitingTimes k 0) where
  default := ⟨fun _ => k, by simp⟩
  uniq t := by
    apply Subtype.ext
    funext a
    have ha : a = (0 : Fin 1) := Fin.eq_zero a
    subst a
    simpa using t.property

/-- A zero-edge waiting sum is the diagonal block power. -/
theorem realSchurGlobalWaitingSum_zero {N : ℕ} (n k : ℕ)
    (B : Fin N → RealSchurBlockData)
    (p : IncreasingBlockPath N 0)
    (z : (Fin N → ℝ) × (SchurEntryIndex N 2 → ℝ)) :
    realSchurGlobalWaitingSum n k B ⟨0,p⟩ z =
      realSchurDataPower (B (p.val 0)) k (z.1 (p.val 0)) := by
  letI := zeroWaitingUniqueGlobal k
  have hwait : (default : SchurWaitingTimes k 0).val 0 = k := by
    simpa using (default : SchurWaitingTimes k 0).property
  rw [realSchurGlobalWaitingSum_eq, Fintype.sum_unique]
  simp [schurPathMatrix, gaussianMatrixChain, hwait]

#print axioms realSchurGlobalWaitingSum_zero
end SpectralRadiusUpperTail

import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

theorem realOrthogonal_entry_abs_le_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : Matrix ι ι ℝ) (hQ : Qᵀ*Q=1) (i j : ι) : |Q i j| ≤ 1 := by
  have hcol : (∑ k : ι, (Q k j)^2)=1 := by
    have h := congrArg (fun A : Matrix ι ι ℝ => A j j) hQ
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq,
      pow_two] using h
  have hsq : (Q i j)^2 ≤ 1 := by
    calc
      _ ≤ ∑ k : ι, (Q k j)^2 :=
        Finset.single_le_sum (fun k _ => sq_nonneg (Q k j)) (Finset.mem_univ i)
      _ = 1 := hcol
  exact (sq_le_one_iff_abs_le_one _).mp hsq

/-- The full real orthogonal frame space is compact, including the
zero-dimensional case. The proof uses the unit bound on every entry. -/
theorem isCompact_realOrthogonalFrames
    (ι : Type*) [Fintype ι] [DecidableEq ι] :
    IsCompact {Q : Matrix ι ι ℝ | Qᵀ*Q=1} := by
  have hclosed : IsClosed {Q : Matrix ι ι ℝ | Qᵀ*Q=1} :=
    isClosed_eq (by fun_prop) continuous_const
  have hbox : IsCompact {Q : Matrix ι ι ℝ | ∀ i j, Q i j ∈ Set.Icc (-1) 1} :=
    isCompact_pi_infinite (fun _ => isCompact_pi_infinite (fun _ => isCompact_Icc))
  apply hbox.of_isClosed_subset hclosed
  intro Q hQ i j
  exact abs_le.mp (realOrthogonal_entry_abs_le_one Q hQ i j)

#print axioms realOrthogonal_entry_abs_le_one
#print axioms isCompact_realOrthogonalFrames
end SpectralRadiusUpperTail

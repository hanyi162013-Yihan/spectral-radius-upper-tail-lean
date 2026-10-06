import SpectralRadiusUpperTail.FiniteArrayMartingale
import Mathlib.Algebra.BigOperators.Fin

namespace SpectralRadiusUpperTail
open scoped BigOperators
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {M N : ℕ}

/-- The terminal serialized sum contains every coordinate exactly once. -/
lemma finiteArray_terminal_sum (d : Fin M → Fin N → Ω → E) (x : Ω) :
    incrementPartialSum (finiteArrayIncrement d) (M*N) x = ∑ i, ∑ j, d i j x := by
  rw [incrementPartialSum, ← Fin.sum_univ_eq_sum_range]
  calc
    _ = ∑ p : Fin M × Fin N, finiteArrayIncrement d (finProdFinEquiv p).val x :=
      (finProdFinEquiv.sum_comp (fun r : Fin (M*N) => finiteArrayIncrement d r.val x)).symm
    _ = ∑ p : Fin M × Fin N, d p.1 p.2 x := by
      apply Finset.sum_congr rfl
      intro p _
      have he : (finProdFinEquiv p).val = p.1.val*N+p.2.val := by
        change p.2.val+N*p.1.val = p.1.val*N+p.2.val
        ac_rfl
      rw [he, finiteArrayIncrement_at]
    _ = ∑ i, ∑ j, d i j x := Fintype.sum_prod_type _

#print axioms finiteArray_terminal_sum
end SpectralRadiusUpperTail

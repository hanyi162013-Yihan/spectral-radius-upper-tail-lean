import SpectralRadiusUpperTail.FiniteArraySum

namespace SpectralRadiusUpperTail
open scoped BigOperators

/-- Every time before the array horizon appears at its exact row-major
coordinate time. This also handles functions depending on that time. -/
lemma finiteArray_time_sum {E : Type*} [AddCommMonoid E] (M N : ℕ) (f : ℕ → E) :
    (∑ r ∈ Finset.range (M*N), f r) = ∑ i : Fin M, ∑ n : Fin N, f (i.val*N+n.val) := by
  rw [← Fin.sum_univ_eq_sum_range]
  calc
    _ = ∑ p : Fin M × Fin N, f (finProdFinEquiv p).val :=
      (finProdFinEquiv.sum_comp (fun r : Fin (M*N) => f r.val)).symm
    _ = ∑ p : Fin M × Fin N, f (p.1.val*N+p.2.val) := by
      apply Finset.sum_congr rfl
      intro p _
      congr 1
      change p.2.val+N*p.1.val = p.1.val*N+p.2.val
      ac_rfl
    _ = _ := Fintype.sum_prod_type _

#print axioms finiteArray_time_sum
end SpectralRadiusUpperTail

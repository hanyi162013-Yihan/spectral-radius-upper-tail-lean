import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped BigOperators

/-- A sum supported strictly above a fixed block index can be indexed by
the upper-triangular subtype without changing its value. -/
theorem schur_strict_upper_sum {N : ℕ} {M : Type*} [AddCommMonoid M]
    (i : Fin N) (f : Fin N → M)
    (hzero : ∀ h, ¬ i < h → f h = 0) :
    (∑ h : {h : Fin N // i < h}, f h.val) = ∑ h : Fin N, f h := by
  classical
  have hz : (∑ h : {h : Fin N // ¬ i < h}, f h.val) = 0 := by
    apply Finset.sum_eq_zero
    intro h _
    exact hzero h.val h.property
  have hsplit := Fintype.sum_subtype_add_sum_subtype (fun h : Fin N => i < h) f
  simpa only [hz, add_zero] using hsplit

#print axioms schur_strict_upper_sum
end SpectralRadiusUpperTail

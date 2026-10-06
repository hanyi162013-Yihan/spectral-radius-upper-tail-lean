import Mathlib.FieldTheory.Separable
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open Polynomial

/-- For a separable real polynomial, counting roots with a predicate is
the cardinality of the corresponding set of distinct real roots. -/
theorem polynomial_simpleRealRoot_countP_eq_ncard
    (p : ℝ[X]) (hp : p ≠ 0) (hsep : p.Separable)
    (P : ℝ → Prop) [DecidablePred P] :
    Multiset.countP P p.roots =
      Set.ncard {x : ℝ | p.IsRoot x ∧ P x} := by
  classical
  have hnodup : (p.roots.filter P).Nodup :=
    (Polynomial.nodup_roots hsep).filter P
  have hset :
      (↑(p.roots.filter P).toFinset : Set ℝ) =
        {x : ℝ | p.IsRoot x ∧ P x} := by
    ext x
    simp [Polynomial.mem_roots hp, and_comm]
  calc
    Multiset.countP P p.roots = (p.roots.filter P).card :=
      Multiset.countP_eq_card_filter P p.roots
    _ = (p.roots.filter P).toFinset.card :=
      (Multiset.toFinset_card_of_nodup hnodup).symm
    _ = Set.ncard {x : ℝ | p.IsRoot x ∧ P x} := by
      rw [← hset]
      exact (Set.ncard_coe_finset _).symm

#print axioms polynomial_simpleRealRoot_countP_eq_ncard
end SpectralRadiusUpperTail

import SpectralRadiusUpperTail.SchurMatrixPathOrthogonality
import SpectralRadiusUpperTail.MatrixOrthogonalSecondMoment
import SpectralRadiusUpperTail.IncreasingPathGaussianSum

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators Matrix.Norms.Frobenius

abbrev SchurEntryIndex (n d : ℕ) := (Fin n × Fin n) × (Fin d × Fin d)

noncomputable def schurPathMatrix {n d : ℕ} (p : AnyIncreasingPath n)
    (D : Fin (p.1+1) → Matrix (Fin d) (Fin d) ℝ) (x : SchurEntryIndex n d → ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  gaussianMatrixChain d p.1 D (fun j => Matrix.of (fun r s => x (increasingPathEdge p.2.val j, (r,s))))

lemma schurPathMatrix_pair_integrable {n d : ℕ} (p q : AnyIncreasingPath n)
    (D : Fin (p.1+1) → Matrix (Fin d) (Fin d) ℝ)
    (E : Fin (q.1+1) → Matrix (Fin d) (Fin d) ℝ) (a b c v : Fin d) :
    Integrable (fun x : SchurEntryIndex n d → ℝ => schurPathMatrix p D x a b *
      schurPathMatrix q E x c v) (Measure.pi (fun _ => standardNormal)) :=
  matrixChain_pair_integrable standardNormal standardNormal_pow_integrable d p.1 q.1 D E
    (fun j r s => (increasingPathEdge p.2.val j, (r,s)))
    (fun j r s => (increasingPathEdge q.2.val j, (r,s))) a b c v

lemma schurPathMatrix_cross_zero {n d : ℕ} (p q : AnyIncreasingPath n)
    (hlast : anyPathLast p = anyPathLast q) (hne : p ≠ q)
    (D : Fin (p.1+1) → Matrix (Fin d) (Fin d) ℝ)
    (E : Fin (q.1+1) → Matrix (Fin d) (Fin d) ℝ) (a b c v : Fin d) :
    (∫ x : SchurEntryIndex n d → ℝ, schurPathMatrix p D x a b *
      schurPathMatrix q E x c v ∂Measure.pi (fun _ => standardNormal)) = 0 := by
  obtain ⟨k, p, hp⟩ := p
  obtain ⟨l, q, hq⟩ := q
  have hm : (∫ z : ℝ, z ∂standardNormal) = 0 := by
    simpa using standardNormal_odd_moment 0
  by_cases hkl : k = l
  · subst l
    have hpq : p ≠ q := by
      intro h
      subst q
      exact hne rfl
    exact (schur_matrix_path_cross_zero standardNormal hm standardNormal_pow_integrable
      Prod.fst p q hp hq hlast hpq D E
      (fun j r s => (increasingPathEdge p j, (r,s)))
      (fun j r s => (increasingPathEdge q j, (r,s)))
      (fun _ _ _ => rfl) (fun _ _ _ => rfl) a b c v).2
  · exact (schur_matrix_path_different_length_cross_zero standardNormal hm
      standardNormal_pow_integrable Prod.fst p q hp hq hkl D E
      (fun j r s => (increasingPathEdge p j, (r,s)))
      (fun j r s => (increasingPathEdge q j, (r,s)))
      (fun _ _ _ => rfl) (fun _ _ _ => rfl) a b c v).2

/-- Exact matrix path Parseval identity in one common iid array.
Different paths may share vertices and random blocks. -/
theorem schur_matrix_path_sum_second_moment {ι : Type*} [Fintype ι] {n d : ℕ}
    (p : ι → AnyIncreasingPath n) (hp : Function.Injective p)
    (hlast : ∀ i j, anyPathLast (p i) = anyPathLast (p j))
    (D : ∀ i, Fin ((p i).1+1) → Matrix (Fin d) (Fin d) ℝ) :
    Integrable (fun x : SchurEntryIndex n d → ℝ => ‖∑ i, schurPathMatrix (p i) (D i) x‖^2)
      (Measure.pi (fun _ => standardNormal)) ∧
    (∫ x : SchurEntryIndex n d → ℝ, ‖∑ i, schurPathMatrix (p i) (D i) x‖^2
      ∂Measure.pi (fun _ => standardNormal)) =
      ∑ i, ∫ x : SchurEntryIndex n d → ℝ, ‖schurPathMatrix (p i) (D i) x‖^2
        ∂Measure.pi (fun _ => standardNormal) := by
  apply matrix_orthogonal_second_moment
  · exact fun i j a b => schurPathMatrix_pair_integrable (p i) (p j) (D i) (D j) a b a b
  · intro i j hij a b
    exact schurPathMatrix_cross_zero (p i) (p j) (hlast i j)
      (fun h => hij (hp h)) (D i) (D j) a b a b

#print axioms schurPathMatrix_cross_zero
#print axioms schur_matrix_path_sum_second_moment
end SpectralRadiusUpperTail

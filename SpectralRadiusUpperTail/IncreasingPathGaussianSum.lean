import SpectralRadiusUpperTail.IncreasingPathCount
import SpectralRadiusUpperTail.IidSimpleWordVariance
import SpectralRadiusUpperTail.FiniteOrthogonalSecondMoment

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators

abbrev AnyIncreasingPath (n : ℕ) := Σ k : ℕ, IncreasingBlockPath n k

def anyPathLast {n : ℕ} (p : AnyIncreasingPath n) : Fin n := p.2.val (Fin.last p.1)
def anyPathWord {n : ℕ} (p : AnyIncreasingPath n) (x : Fin n × Fin n → ℝ) : ℝ :=
  ∏ j, x (increasingPathEdge p.2.val j)

lemma anyPath_cross_zero {n : ℕ} (p q : AnyIncreasingPath n)
    (hlast : anyPathLast p = anyPathLast q) (hne : p ≠ q) :
    (∫ x : Fin n × Fin n → ℝ, anyPathWord p x*anyPathWord q x
      ∂Measure.pi (fun _ => standardNormal)) = 0 := by
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
    simpa only [anyPathWord, star_trivial] using
      increasingPath_cross_moment_zero standardNormal hm hp hq hlast hpq
  · simpa only [anyPathWord, star_trivial] using
      increasingPath_different_length_cross_zero standardNormal hm hp hq hkl

/-- A finite weighted sum of distinct increasing Gaussian paths with a
common terminal block has exactly the sum of its diagonal variances.
Path lengths may differ, and shared vertices/edges are allowed. -/
theorem increasingPath_gaussian_sum_second_moment {ι : Type*} [Fintype ι]
    {n : ℕ} (p : ι → AnyIncreasingPath n) (hp : Function.Injective p)
    (hlast : ∀ i j, anyPathLast (p i) = anyPathLast (p j)) (c : ι → ℝ) :
    Integrable (fun x : Fin n × Fin n → ℝ => (∑ i, c i*anyPathWord (p i) x)^2)
      (Measure.pi (fun _ => standardNormal)) ∧
    (∫ x : Fin n × Fin n → ℝ, (∑ i, c i*anyPathWord (p i) x)^2
      ∂Measure.pi (fun _ => standardNormal)) = ∑ i, (c i)^2 := by
  have hi (i j : ι) : Integrable (fun x : Fin n × Fin n → ℝ =>
      (c i*anyPathWord (p i) x)*(c j*anyPathWord (p j) x))
      (Measure.pi (fun _ => standardNormal)) := by
    have h := (iid_real_word_pair_integrable standardNormal standardNormal_pow_integrable
      (increasingPathEdge (p i).2.val) (increasingPathEdge (p j).2.val)).const_mul (c i*c j)
    convert h using 1
    funext x
    dsimp [anyPathWord]
    ring
  have ho (i j : ι) (hij : i ≠ j) :
      (∫ x : Fin n × Fin n → ℝ, (c i*anyPathWord (p i) x)*(c j*anyPathWord (p j) x)
        ∂Measure.pi (fun _ => standardNormal)) = 0 := by
    have he (x : Fin n × Fin n → ℝ) :
        (c i*anyPathWord (p i) x)*(c j*anyPathWord (p j) x) =
          (c i*c j)*(anyPathWord (p i) x*anyPathWord (p j) x) := by ring
    simp_rw [he]
    rw [integral_const_mul, anyPath_cross_zero (p i) (p j) (hlast i j)
      (fun h => hij (hp h)), mul_zero]
  obtain ⟨hint, heq⟩ := finite_orthogonal_second_moment
    (Measure.pi (fun _ : Fin n × Fin n => standardNormal))
    (fun i x => c i*anyPathWord (p i) x) hi ho
  refine ⟨hint, heq.trans ?_⟩
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [mul_pow]
  rw [integral_const_mul]
  have hv := gaussian_simple_word_second_moment (increasingPathEdge (p i).2.val)
    (increasingPathEdge_injective (p i).2.property)
  change (c i)^2*(∫ x, (∏ j, x (increasingPathEdge (p i).2.val j))^2
    ∂Measure.pi (fun _ => standardNormal)) = (c i)^2
  rw [hv, mul_one]

#print axioms anyPath_cross_zero
#print axioms increasingPath_gaussian_sum_second_moment
end SpectralRadiusUpperTail

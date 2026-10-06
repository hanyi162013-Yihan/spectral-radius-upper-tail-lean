import SpectralRadiusUpperTail.GaussianComplexCharpolyMomentCardinality
import SpectralRadiusUpperTail.GinibrePoissonSharp
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators

private theorem choose_factorial_quotient
    (m j : ℕ) (hj : j ≤ m) :
    (((m.choose (m-j) * (m-j).factorial : ℕ) : ℝ)) =
      (m.factorial : ℝ)/(j.factorial : ℝ) := by
  have h := Nat.choose_mul_factorial_mul_factorial (Nat.sub_le m j)
  have hsub : m-(m-j) = j := by omega
  rw [hsub] at h
  have hR :
      (((m.choose (m-j) * (m-j).factorial : ℕ) : ℝ)) *
        (j.factorial : ℝ) = (m.factorial : ℝ) := by
    exact_mod_cast h
  exact (eq_div_iff (by positivity : (j.factorial : ℝ) ≠ 0)).mpr hR

/-- Edelman's finite Poisson factor follows directly from principal-minor
orthogonality, without a real-Schur eigenvalue integration. -/
theorem gaussian_real_complex_charpoly_poisson_moment
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ℂ) :
    (∫ z : ι × ι → ℝ,
      Complex.normSq
        (((Matrix.of z.curry).map Complex.ofRealHom).charpoly.eval w)
      ∂Measure.pi (fun _ => standardNormal)) =
      ((Fintype.card ι).factorial : ℝ) *
        ginibreExpPartial (Fintype.card ι+1) (Complex.normSq w) := by
  classical
  let m := Fintype.card ι
  let q := Complex.normSq w
  rw [gaussian_real_complex_charpoly_second_moment_cardinality]
  unfold ginibreExpPartial
  rw [Finset.mul_sum]
  rw [← Finset.sum_range_reflect
    (fun k => (((m.choose k * k.factorial : ℕ) : ℝ)) * q^(m-k)) (m+1)]
  apply Finset.sum_congr rfl
  intro j hj
  have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hsub : m-(m-j) = j := by omega
  simp only [Nat.add_sub_cancel_right]
  rw [hsub, choose_factorial_quotient m j hjm]
  ring

#print axioms gaussian_real_complex_charpoly_poisson_moment
end SpectralRadiusUpperTail

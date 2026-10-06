import SpectralRadiusUpperTail.ComplexDiagonalSphereIntegral
import SpectralRadiusUpperTail.ExponentialCoordinateSplit
import SpectralRadiusUpperTail.ExponentialWitnessOuterIntegral
import SpectralRadiusUpperTail.ExponentialWitnessPrefactor

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

/-- A direct exponential-rate witness, avoiding a simplex-density Jacobian. -/
lemma complex_diagonal_exponential_witness (m : ℕ) (u : ℝ) (hu : 0 < u)
    (h : Fin (m+1) → ℝ) (hh : ∀ j, 0 ≤ h j) (i : Fin (m+1)) (hmin : ∀ j, h i ≤ h j) :
    ENNReal.ofReal (Real.exp (-((m+1 : ℕ) : ℝ)*h i/u-((m+1 : ℕ) : ℝ))*
      u^(m+1)/(∏ j, (h j+2*u))) ≤
        complexDiagonalSphereIntegral (m+1) (((m+1 : ℕ) : ℝ)/u) h := by
  let N : ℝ := ((m+1 : ℕ) : ℝ)
  let g : Fin m → ℝ := fun j => h (i.succAbove j)
  let r : Fin m → ℝ := fun j => (g j+2*u)/(2*u)
  have hr (j : Fin m) : 1 ≤ r j := by
    dsimp [r, g]
    apply (le_div_iff₀ (by positivity : 0 < 2*u)).mpr
    linarith [hh (i.succAbove j)]
  have hdom (j : Fin m) : (g j-h i)/(2*u) ≤ r j := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith [hh i]
  have hout := exponential_witness_outer_integral m N u (h i) g r (by dsimp [N]; positivity)
    (by dsimp [N]; push_cast; linarith) hu (fun j => hmin (i.succAbove j)) hr hdom
  rw [complexDiagonalSphereIntegral_exponential (m+1) (by omega),
    exponential_normalized_integral_split m i (((m+1 : ℕ) : ℝ)) u h]
  apply le_trans _ hout
  have hp := exponential_witness_prefactor m u (h i) g hu (hh i) (fun j => hh (i.succAbove j))
  have hpre := ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_left hp (Real.exp_pos (-N*h i/u-N)).le)
  have hhalf : ENNReal.ofReal (1/2 : ℝ) = (1/2 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have he : (∏ j : Fin (m+1), (h j+2*u)) = (h i+2*u)*∏ j : Fin m, (g j+2*u) := by
    simpa only [g] using Fin.prod_univ_succAbove (fun j => h j+2*u) i
  rw [he]
  convert! hpre using 1
  · dsimp [N]
    congr 1 <;> ring
  · rw [← hhalf, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    dsimp [r]
    ring

#print axioms complex_diagonal_exponential_witness
end SpectralRadiusUpperTail

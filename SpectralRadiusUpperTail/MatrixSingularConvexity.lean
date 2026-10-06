import SpectralRadiusUpperTail.DilationSpectralSum
import SpectralRadiusUpperTail.FiniteHermitianDilation
import SpectralRadiusUpperTail.HermitianSpectralLipschitz
import SpectralRadiusUpperTail.ConvexEvenExtension

namespace SpectralRadiusUpperTail
open scoped BigOperators NNReal Matrix.Norms.Frobenius

noncomputable def matrixSingularSum {n : ℕ} (f : ℝ → ℝ)
    (A : Matrix (Fin n) (Fin n) ℂ) : ℝ := ∑ i, f (gramSingularMagnitude A i)

lemma finiteHermitianDilation_spectral_sum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (f : ℝ → ℝ) :
    (∑ i, f |(finiteHermitianDilation_isHermitian A).eigenvalues i|) = 2*matrixSingularSum f A := by
  have hh := hermitian_spectral_sum_charpoly (finiteHermitianDilation A) (hermitianDilation A)
    (finiteHermitianDilation_isHermitian A) (hermitianDilation_isHermitian A)
    (Matrix.charpoly_reindex finSumFinEquiv (hermitianDilation A)) (fun t => f |t|)
  exact hh.trans (hermitianDilation_spectral_sum A f)

lemma matrixSingularSum_convex (n : ℕ) (f : ℝ → ℝ)
    (hf : ConvexOn ℝ (Set.Ici 0) f) (hm : MonotoneOn f (Set.Ici 0)) :
    ConvexOn ℝ Set.univ (matrixSingularSum (n := n) f) := by
  refine ⟨convex_univ, ?_⟩
  intro A hA B hB a b ha hb hab
  have hM : ((a : ℂ) • finiteHermitianDilation A+
      (b : ℂ) • finiteHermitianDilation B).IsHermitian := by
    rw [← finiteHermitianDilation_combination]
    exact finiteHermitianDilation_isHermitian _
  have hh := hermitian_spectral_sum_convex (finiteHermitianDilation A) (finiteHermitianDilation B)
    (finiteHermitianDilation_isHermitian A) (finiteHermitianDilation_isHermitian B)
    a b ha hb hab hM (fun t => f |t|) (convex_even_extension f hf hm)
  have hleft : (∑ i, f |hM.eigenvalues i|) =
      2*matrixSingularSum f ((a : ℂ) • A+(b : ℂ) • B) := by
    have he := hermitian_spectral_sum_charpoly
      ((a : ℂ) • finiteHermitianDilation A+(b : ℂ) • finiteHermitianDilation B)
      (finiteHermitianDilation ((a : ℂ) • A+(b : ℂ) • B))
      hM (finiteHermitianDilation_isHermitian _)
      (congrArg Matrix.charpoly (finiteHermitianDilation_combination A B a b).symm)
      (fun t => f |t|)
    exact he.trans (finiteHermitianDilation_spectral_sum _ f)
  rw [hleft, finiteHermitianDilation_spectral_sum A f,
    finiteHermitianDilation_spectral_sum B f] at hh
  change matrixSingularSum f (a • A+b • B) ≤ a*matrixSingularSum f A+b*matrixSingularSum f B
  have hclean : 2*matrixSingularSum f (a • A+b • B) ≤
      2*(a*matrixSingularSum f A+b*matrixSingularSum f B) := by
    convert! hh using 1 <;> ring
  linarith only [hclean]

lemma sqrt_double_dimension (n : ℕ) :
    Real.sqrt ((n : ℝ)+(n : ℝ))*Real.sqrt 2 = 2*Real.sqrt (n : ℝ) := by
  rw [← two_mul, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    _ = (Real.sqrt 2)^2*Real.sqrt (n : ℝ) := by ring
    _ = _ := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

lemma matrixSingularSum_lipschitz_bound {n : ℕ} (f : ℝ → ℝ)
    (hf : ConvexOn ℝ (Set.Ici 0) f) (hm : MonotoneOn f (Set.Ici 0))
    (C : ℝ≥0) (hLip : LipschitzOnWith C f (Set.Ici 0))
    (A B : Matrix (Fin n) (Fin n) ℂ) :
    |matrixSingularSum f A-matrixSingularSum f B| ≤
      (C : ℝ)*Real.sqrt (n : ℝ)*‖A-B‖ := by
  have hh := hermitian_spectral_sum_lipschitz (finiteHermitianDilation A) (finiteHermitianDilation B)
    (finiteHermitianDilation_isHermitian A) (finiteHermitianDilation_isHermitian B)
    (fun t => f |t|) (convex_even_extension f hf hm) C (lipschitz_even_extension f C hLip)
  rw [finiteHermitianDilation_spectral_sum A f, finiteHermitianDilation_spectral_sum B f,
    ← finiteHermitianDilation_sub, finiteHermitianDilation_frobenius] at hh
  have he : |2*matrixSingularSum f A-2*matrixSingularSum f B| =
      2*|matrixSingularSum f A-matrixSingularSum f B| := by
    rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [he] at hh
  simp only [Nat.cast_add] at hh
  have hc : (C : ℝ)*Real.sqrt ((n : ℝ)+(n : ℝ))*(Real.sqrt 2*‖A-B‖) =
      2*((C : ℝ)*Real.sqrt (n : ℝ)*‖A-B‖) := by
    calc
      _ = (C : ℝ)*(Real.sqrt ((n : ℝ)+(n : ℝ))*Real.sqrt 2)*‖A-B‖ := by ring
      _ = _ := by rw [sqrt_double_dimension]; ring
  rw [hc] at hh
  linarith

lemma matrixSingularSum_lipschitz (n : ℕ) (f : ℝ → ℝ)
    (hf : ConvexOn ℝ (Set.Ici 0) f) (hm : MonotoneOn f (Set.Ici 0))
    (C : ℝ≥0) (hLip : LipschitzOnWith C f (Set.Ici 0)) :
    LipschitzWith (C*Real.toNNReal (Real.sqrt (n : ℝ))) (matrixSingularSum (n := n) f) := by
  apply LipschitzWith.of_dist_le_mul
  intro A B
  simpa only [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs, NNReal.coe_mul,
    Real.coe_toNNReal _ (Real.sqrt_nonneg _), mul_assoc] using
      matrixSingularSum_lipschitz_bound f hf hm C hLip A B

#print axioms finiteHermitianDilation_spectral_sum
#print axioms matrixSingularSum_convex
#print axioms sqrt_double_dimension
#print axioms matrixSingularSum_lipschitz_bound
#print axioms matrixSingularSum_lipschitz
end SpectralRadiusUpperTail

import SpectralRadiusUpperTail.HaarSphereDirection
import SpectralRadiusUpperTail.MatrixSqrtEnergy
import SpectralRadiusUpperTail.PositiveWeightNormalizer

namespace SpectralRadiusUpperTail
open MeasureTheory Metric
open scoped ENNReal ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable (𝕂 : Type*) [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂]

noncomputable def sphereQuadraticIntegral (n : ℕ) (c : ℝ) (H : Matrix (Fin n) (Fin n) 𝕂) : ℝ :=
  ∫ v : sphere (0 : EuclideanSpace 𝕂 (Fin n)) 1,
    Real.exp (-c*RCLike.re (inner 𝕂 v.val (Matrix.toEuclideanCLM (𝕜 := 𝕂) H v.val)))
    ∂haarSphereProbability (volume : Measure (EuclideanSpace 𝕂 (Fin n)))

lemma sphereQuadratic_integrable (n : ℕ) (hn : 0 < n) (c : ℝ) (hc : 0 ≤ c)
    (H : Matrix (Fin n) (Fin n) 𝕂) (hH : H.PosSemidef) :
    Integrable (fun v : sphere (0 : EuclideanSpace 𝕂 (Fin n)) 1 =>
      Real.exp (-c*RCLike.re (inner 𝕂 v.val (Matrix.toEuclideanCLM (𝕜 := 𝕂) H v.val))))
      (haarSphereProbability (volume : Measure (EuclideanSpace 𝕂 (Fin n)))) := by
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  letI := haarSphereProbability_probability (volume : Measure (EuclideanSpace 𝕂 (Fin n)))
  apply Integrable.of_bound (by fun_prop) 1
  apply Filter.Eventually.of_forall
  intro v
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_one_iff.mpr
  rw [← matrix_sqrt_energy H hH]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc) (sq_nonneg _)

lemma sphereQuadraticIntegral_pos (n : ℕ) (hn : 0 < n) (c : ℝ) (hc : 0 ≤ c)
    (H : Matrix (Fin n) (Fin n) 𝕂) (hH : H.PosSemidef) :
    0 < sphereQuadraticIntegral 𝕂 n c H := by
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  letI := haarSphereProbability_probability (volume : Measure (EuclideanSpace 𝕂 (Fin n)))
  exact integral_exp_pos (sphereQuadratic_integrable 𝕂 n hn c hc H hH)

lemma sphereQuadraticIntegral_lintegral (n : ℕ) (hn : 0 < n) (c : ℝ) (hc : 0 ≤ c)
    (H : Matrix (Fin n) (Fin n) 𝕂) (hH : H.PosSemidef) :
    ENNReal.ofReal (sphereQuadraticIntegral 𝕂 n c H) =
      ∫⁻ v : sphere (0 : EuclideanSpace 𝕂 (Fin n)) 1,
        ENNReal.ofReal (Real.exp (-c*RCLike.re (inner 𝕂 v.val (Matrix.toEuclideanCLM (𝕜 := 𝕂) H v.val))))
        ∂haarSphereProbability (volume : Measure (EuclideanSpace 𝕂 (Fin n))) :=
  ofReal_integral_eq_lintegral_ofReal (sphereQuadratic_integrable 𝕂 n hn c hc H hH)
    (Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le))

#print axioms sphereQuadraticIntegral
#print axioms sphereQuadratic_integrable
#print axioms sphereQuadraticIntegral_pos
#print axioms sphereQuadraticIntegral_lintegral
end SpectralRadiusUpperTail

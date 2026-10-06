import SpectralRadiusUpperTail.GaussianRowRegressionMoment
import SpectralRadiusUpperTail.TriangularNorm

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators Matrix.Norms.Frobenius
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂] {N : ℕ}

/-- Actual independent Gaussian-soft tilted row laws, allowing different targets. -/
noncomputable def gaussianTiltedMatrixLaw (μ : Measure 𝕂) (a : ℝ) (v : ℕ → 𝕂)
    (t : Fin N → 𝕂) : Measure (Fin N → Fin N → 𝕂) :=
  Measure.pi (fun i => gaussianFiniteRowLaw μ a (fun j : Fin N => v j.val) (t i))

/-- The actual regression residual array with the matrix normalization. -/
noncomputable def gaussianRegressionMatrix (μ : Measure 𝕂) (a : ℝ) (v : ℕ → 𝕂)
    (t : Fin N → 𝕂) (η : ℝ) (x : Fin N → Fin N → 𝕂) : Matrix (Fin N) (Fin N) 𝕂 :=
  fun i j => (1/Real.sqrt (N : ℝ) : ℝ) • gaussianRowRegression μ a v j (t i) η (x i)

omit [BorelSpace 𝕂] [SecondCountableTopology 𝕂] in
lemma gaussianRegressionMatrix_norm_sq (μ : Measure 𝕂) (a : ℝ) (v : ℕ → 𝕂)
    (t : Fin N → 𝕂) (η : ℝ) (x : Fin N → Fin N → 𝕂) :
    ‖gaussianRegressionMatrix μ a v t η x‖^2 =
      (1/(N : ℝ))*(∑ i, ∑ j, ‖gaussianRowRegression μ a v j (t i) η (x i)‖^2) := by
  rw [frobenius_norm_sq_eq_sum]
  simp only [gaussianRegressionMatrix, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    div_pow, one_pow, Real.sq_sqrt (Nat.cast_nonneg N), Finset.mul_sum]

lemma gaussianTiltedMatrixLaw_probability (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (hm : (∫ x : 𝕂, x ∂μ) = 0)
    (hvar : (∫ x : 𝕂, ‖x‖^2 ∂μ) = 1) (v : ℕ → 𝕂)
    (hv : ∑ j : Fin N, ‖v j.val‖^2 ≤ 1) (a : ℝ) (ha : 0 < a) (t : Fin N → 𝕂) :
    IsProbabilityMeasure (gaussianTiltedMatrixLaw μ a v t) := by
  have (i : Fin N) : IsProbabilityMeasure (gaussianFiniteRowLaw μ a (fun j : Fin N => v j.val) (t i)) :=
    gaussianFiniteRowLaw_probability μ hX hm hvar v hv a ha (t i)
  unfold gaussianTiltedMatrixLaw
  infer_instance

/-- Each actual tilted row is precisely the coordinate marginal of the array. -/
lemma gaussianTiltedMatrixLaw_row (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (hm : (∫ x : 𝕂, x ∂μ) = 0)
    (hvar : (∫ x : 𝕂, ‖x‖^2 ∂μ) = 1) (v : ℕ → 𝕂)
    (hv : ∑ j : Fin N, ‖v j.val‖^2 ≤ 1) (a : ℝ) (ha : 0 < a) (t : Fin N → 𝕂) (i : Fin N) :
    (gaussianTiltedMatrixLaw μ a v t).map (fun x => x i) =
      gaussianFiniteRowLaw μ a (fun j : Fin N => v j.val) (t i) := by
  have (k : Fin N) : IsProbabilityMeasure (gaussianFiniteRowLaw μ a (fun j : Fin N => v j.val) (t k)) :=
    gaussianFiniteRowLaw_probability μ hX hm hvar v hv a ha (t k)
  exact (measurePreserving_eval _ i).map_eq

/-- The actual normalized Frobenius second moment is the average of the
actual row errors. This is an equality of integrals over the constructed law. -/
theorem gaussianRegressionMatrix_secondMoment (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (hm : (∫ x : 𝕂, x ∂μ) = 0)
    (hvar : (∫ x : 𝕂, ‖x‖^2 ∂μ) = 1) (v : ℕ → 𝕂)
    (hv : ∑ j : Fin N, ‖v j.val‖^2 ≤ 1) (a : ℝ) (ha : 0 < a)
    (t : Fin N → 𝕂) (η : ℝ)
    (hi : ∀ i : Fin N, Integrable (fun x => ∑ j : Fin N, ‖gaussianRowRegression μ a v j (t i) η x‖^2)
      (gaussianFiniteRowLaw μ a (fun j : Fin N => v j.val) (t i))) :
    Integrable (fun x => ‖gaussianRegressionMatrix μ a v t η x‖^2) (gaussianTiltedMatrixLaw μ a v t) ∧
    (∫ x, ‖gaussianRegressionMatrix μ a v t η x‖^2 ∂gaussianTiltedMatrixLaw μ a v t) =
      (1/(N : ℝ))*(∑ i, ∫ x, ∑ j : Fin N, ‖gaussianRowRegression μ a v j (t i) η x‖^2
        ∂gaussianFiniteRowLaw μ a (fun j : Fin N => v j.val) (t i)) := by
  have (i : Fin N) : IsProbabilityMeasure (gaussianFiniteRowLaw μ a (fun j : Fin N => v j.val) (t i)) :=
    gaussianFiniteRowLaw_probability μ hX hm hvar v hv a ha (t i)
  have hi' (i : Fin N) : Integrable (fun x : Fin N → Fin N → 𝕂 =>
      ∑ j : Fin N, ‖gaussianRowRegression μ a v j (t i) η (x i)‖^2) (gaussianTiltedMatrixLaw μ a v t) :=
    by
      convert! (measurePreserving_eval
        (fun k : Fin N => gaussianFiniteRowLaw μ a (fun j : Fin N => v j.val) (t k)) i).integrable_comp_of_integrable (hi i) using 1
  simp_rw [gaussianRegressionMatrix_norm_sq]
  refine ⟨(integrable_finsetSum _ (fun i _ => hi' i)).const_mul _, ?_⟩
  rw [integral_const_mul, integral_finsetSum _ (fun i _ => hi' i)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hmarg := gaussianTiltedMatrixLaw_row μ hX hm hvar v hv a ha t i
  have hg : AEStronglyMeasurable (fun x => ∑ j : Fin N, ‖gaussianRowRegression μ a v j (t i) η x‖^2)
      ((gaussianTiltedMatrixLaw μ a v t).map (fun x => x i)) := by
    rw [hmarg]
    exact (hi i).aestronglyMeasurable
  have hh := integral_map (μ := gaussianTiltedMatrixLaw μ a v t)
    (measurable_pi_apply i).aemeasurable hg
  rw [hmarg] at hh
  exact hh.symm

#print axioms gaussianRegressionMatrix_norm_sq
#print axioms gaussianRegressionMatrix_secondMoment
end SpectralRadiusUpperTail

import SpectralRadiusUpperTail.GaussianEuclideanDensity
import SpectralRadiusUpperTail.GaussianWholeDirection
import Mathlib.Probability.Distributions.Gaussian.Multivariate

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory WithLp Metric
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

lemma stdGaussian_eq_radial_normalizedTilt :
    stdGaussian E = normalizedTilt (volume : Measure E)
      (fun x => ENNReal.ofReal (Real.exp (-(1/2)*‖x‖^2))) := by
  let b := stdOrthonormalBasis ℝ E
  have hd : 0 < Module.finrank ℝ E := Module.finrank_pos
  have he := standardNormal_euclidean_eq_normalizedTilt (Module.finrank ℝ E) hd
  have hg : (Measure.pi (fun _ : Fin (Module.finrank ℝ E) => standardNormal)).map (toLp 2) =
      stdGaussian (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) := by
    exact map_pi_eq_stdGaussian
  rw [hg] at he
  have hm := congrArg (fun ρ : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) =>
    ρ.map b.repr.symm) he
  rw [stdGaussian_map] at hm
  have ht := normalizedTilt_map_measurePreserving
    (volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))
    (volume : Measure E) b.repr.symm b.measurePreserving_repr_symm
    (fun x => ENNReal.ofReal (Real.exp (-(1/2)*‖x‖^2))) (by fun_prop)
    (gaussian_norm_normalizer_bounds (volume : Measure E) (1/2) (by norm_num)).1
  simp only [LinearIsometryEquiv.norm_map] at ht
  exact hm.trans ht

lemma stdGaussian_direction_eq_haarSphere :
    (stdGaussian E).map (fun x => ‖x‖⁻¹ • x) =
      (haarSphereProbability (volume : Measure E)).map Subtype.val := by
  rw [stdGaussian_eq_radial_normalizedTilt]
  exact gaussian_whole_direction_eq_haarSphere volume (1/2) (by norm_num)

#print axioms stdGaussian_eq_radial_normalizedTilt
#print axioms stdGaussian_direction_eq_haarSphere
end SpectralRadiusUpperTail

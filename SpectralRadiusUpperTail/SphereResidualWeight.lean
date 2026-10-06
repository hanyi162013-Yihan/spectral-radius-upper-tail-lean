import SpectralRadiusUpperTail.FlatHaarWeightBound
import SpectralRadiusUpperTail.SphereQuadraticIntegral
import SpectralRadiusUpperTail.ResidualGram

namespace SpectralRadiusUpperTail
open MeasureTheory WithLp Metric
open scoped ENNReal ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂]

lemma fullSphereWeight_eq_quadratic (n : ℕ) (hn : 0 < n) (a : ℝ) (ha : 0 < a)
    (b : 𝕂) (x : Fin n → Fin n → 𝕂) :
    fullSpectralSphereWeight n a b x =
      ENNReal.ofReal (sphereQuadraticIntegral 𝕂 n ((n : ℝ)/a) (spectralResidualGram x b)) := by
  rw [fullSpectralSphereWeight_eq_sphere,sphereQuadraticIntegral_lintegral 𝕂 n hn _
    (div_nonneg (Nat.cast_nonneg n) ha.le) _ (spectralResidualGram_posSemidef x b)]
  apply lintegral_congr
  intro v
  unfold spectralResidualGram
  rw [matrix_gram_energy]
  congr 2
  change -(n : ℝ)*‖toLp 2
      ((normalizedArray x-b • (1 : Matrix (Fin n) (Fin n) 𝕂)).mulVec (ofLp v.val))‖^2/a =
    -((n : ℝ)/a)*‖toLp 2
      ((normalizedArray x-b • (1 : Matrix (Fin n) (Fin n) 𝕂)).mulVec (ofLp v.val))‖^2
  ring

noncomputable def regularizedResidualLogDet {n : ℕ} (x : Fin n → Fin n → 𝕂) (b : 𝕂) (s : ℝ) : ℝ :=
  Real.log ‖(spectralResidualGram x b+(s : 𝕂) • (1 : Matrix (Fin n) (Fin n) 𝕂)).det‖

lemma regularizedResidualLogDet_measurable (n : ℕ) (b : 𝕂) (s : ℝ) :
    Measurable (fun x : Fin n → Fin n → 𝕂 => regularizedResidualLogDet x b s) := by
  unfold regularizedResidualLogDet spectralResidualGram
  have hd : Continuous (fun x : Fin n → Fin n → 𝕂 =>
      ((normalizedArray x-b • (1 : Matrix (Fin n) (Fin n) 𝕂)).conjTranspose *
        (normalizedArray x-b • (1 : Matrix (Fin n) (Fin n) 𝕂))+
        (s : 𝕂) • (1 : Matrix (Fin n) (Fin n) 𝕂)).det) := by
    apply Continuous.matrix_det
    unfold normalizedArray
    fun_prop
  exact Real.measurable_log.comp hd.norm.measurable

#print axioms fullSphereWeight_eq_quadratic
#print axioms regularizedResidualLogDet
#print axioms regularizedResidualLogDet_measurable
end SpectralRadiusUpperTail

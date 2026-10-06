import SpectralRadiusUpperTail.SphereResidualWeight
import SpectralRadiusUpperTail.RealComplexIidLaw

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators

lemma regularizedResidualLogDet_complexify {n : ℕ}
    (x : Fin n → Fin n → ℝ) (b s : ℝ) :
    regularizedResidualLogDet x b s =
      regularizedResidualLogDet (fun i j => (x i j : ℂ)) (b : ℂ) s := by
  let f : Matrix (Fin n) (Fin n) ℝ →+* Matrix (Fin n) (Fin n) ℂ := Complex.ofRealHom.mapMatrix
  have hfstar (M : Matrix (Fin n) (Fin n) ℝ) : f M.conjTranspose = (f M).conjTranspose := by
    ext i j
    change ((star (M j i) : ℝ) : ℂ) = star (M j i : ℂ)
    simp
  have hfscalar (t : ℝ) : f (t • 1) = (t : ℂ) • 1 := by
    ext i j
    change ((t * (1 : Matrix (Fin n) (Fin n) ℝ) i j : ℝ) : ℂ) =
      (t : ℂ)*(1 : Matrix (Fin n) (Fin n) ℂ) i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have hfnorm : f (normalizedArray x) = normalizedArray (fun i j => (x i j : ℂ)) := by
    ext i j
    change (((1/Real.sqrt (n : ℝ))*x i j : ℝ) : ℂ) = (1/Real.sqrt (n : ℝ) : ℝ) • (x i j : ℂ)
    rw [Complex.ofReal_mul, RCLike.real_smul_eq_coe_mul]
    rfl
  have hG : f (spectralResidualGram x b+s • (1 : Matrix (Fin n) (Fin n) ℝ)) =
      spectralResidualGram (fun i j => (x i j : ℂ)) (b : ℂ)+
        (s : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    unfold spectralResidualGram
    rw [map_add, map_mul, hfstar, map_sub, hfnorm, hfscalar, hfscalar]
  unfold regularizedResidualLogDet
  change Real.log ‖(spectralResidualGram x b+s • (1 : Matrix (Fin n) (Fin n) ℝ)).det‖ =
    Real.log ‖(spectralResidualGram (fun i j => (x i j : ℂ)) (b : ℂ)+
      (s : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).det‖
  rw [← hG]
  change Real.log ‖(spectralResidualGram x b+s • (1 : Matrix (Fin n) (Fin n) ℝ)).det‖ =
    Real.log ‖(Complex.ofRealHom.mapMatrix (spectralResidualGram x b+s • 1)).det‖
  rw [← RingHom.map_det]
  simp only [Complex.ofRealHom_eq_coe, Complex.norm_real]

lemma nested_iid_complexifiedLaw (μ : Measure ℝ) [IsProbabilityMeasure μ] (n : ℕ) :
    (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).map
      (fun x : Fin n → Fin n → ℝ => fun i j => (x i j : ℂ)) =
      Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => complexifiedLaw μ)) := by
  have hh := Measure.pi_map_pi (μ := fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))
    (f := fun _ : Fin n => fun x : Fin n → ℝ => fun j => (x j : ℂ))
    (fun _ => (show Measurable (fun x : Fin n → ℝ => fun j => (x j : ℂ)) by fun_prop).aemeasurable)
  simpa only [iid_complexifiedLaw] using hh

lemma real_regularizedResidualLogDet_integral_complexify (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (n : ℕ) (b s : ℝ) :
    (∫ x : Fin n → Fin n → ℝ, regularizedResidualLogDet x b s/(n : ℝ)
      ∂Measure.pi (fun _ => Measure.pi (fun _ => μ))) =
    ∫ x : Fin n → Fin n → ℂ, regularizedResidualLogDet x (b : ℂ) s/(n : ℝ)
      ∂Measure.pi (fun _ => Measure.pi (fun _ => complexifiedLaw μ)) := by
  rw [← nested_iid_complexifiedLaw μ n, integral_map
    (show AEMeasurable (fun x : Fin n → Fin n → ℝ => fun i j => (x i j : ℂ))
      (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))) from
      (show Measurable (fun x : Fin n → Fin n → ℝ => fun i j => (x i j : ℂ)) by fun_prop).aemeasurable)
    ((regularizedResidualLogDet_measurable n (b : ℂ) s).div_const (n : ℝ)).aestronglyMeasurable]
  simp only [regularizedResidualLogDet_complexify]

#print axioms regularizedResidualLogDet_complexify
#print axioms nested_iid_complexifiedLaw
#print axioms real_regularizedResidualLogDet_integral_complexify
end SpectralRadiusUpperTail

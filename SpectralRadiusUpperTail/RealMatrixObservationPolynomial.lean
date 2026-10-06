import SpectralRadiusUpperTail.RealMatrixObservationWitness
import SpectralRadiusUpperTail.RealPolynomialZeroSets
import SpectralRadiusUpperTail.GaussianMatrixAbsoluteContinuity

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped Matrix

noncomputable def realObservationPolynomial (n : ℕ) (k : Fin n) :
    MvPolynomial (Fin n × Fin n) ℝ :=
  (Matrix.of (fun i j : Fin n =>
    ((Matrix.of (fun a b : Fin n => MvPolynomial.X (a,b)))^i.val) k j)).det

theorem realObservationPolynomial_eval (n : ℕ) (k : Fin n)
    (a : (Fin n × Fin n) → ℝ) :
    MvPolynomial.eval a (realObservationPolynomial n k) =
      (realMatrixObservation n (Matrix.of a.curry) k).det := by
  let U : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) ℝ) :=
    fun i j => MvPolynomial.X (i,j)
  let φ := MvPolynomial.eval₂Hom (RingHom.id ℝ) a
  have hU : U.map φ = Matrix.of a.curry := by
    ext i j
    exact MvPolynomial.eval₂_X (RingHom.id ℝ) a (i,j)
  change φ (Matrix.of (fun i j : Fin n => (U^i.val) k j)).det = _
  rw [RingHom.map_det]
  congr 1
  ext i j
  have hh := Matrix.map_pow U φ i.val
  rw [hU] at hh
  exact congrFun (congrFun hh k) j

theorem realObservationPolynomial_ne_zero (n : ℕ) (k : Fin n) :
    realObservationPolynomial n k ≠ 0 := by
  let a : (Fin n × Fin n) → ℝ := fun ij => (finRotate n).permMatrix ℝ ij.1 ij.2
  have ha : MvPolynomial.eval a (realObservationPolynomial n k) ≠ 0 := by
    rw [realObservationPolynomial_eval]
    exact realMatrixObservation_cycle_det_ne_zero n k
  intro hzero
  exact ha (by rw [hzero, map_zero])

theorem realMatrixObservation_det_ne_zero_ae_volume (n : ℕ) :
    ∀ᵐ a : (Fin n × Fin n) → ℝ,
      ∀ k : Fin n, (realMatrixObservation n (Matrix.of a.curry) k).det ≠ 0 := by
  apply ae_all_iff.mpr
  intro k
  have hh := mvPolynomial_eval_ne_zero_ae_pi
    (fun _ : Fin n × Fin n => (volume : Measure ℝ))
    (realObservationPolynomial n k) (realObservationPolynomial_ne_zero n k)
  filter_upwards [hh] with a ha
  rwa [realObservationPolynomial_eval] at ha

/-- Under the actual real Gaussian law, every real eigenvector has all
coordinates nonzero, simultaneously over the eigenvalues and vectors. -/
theorem realGaussian_eigenvectors_coordinates_ne_zero_ae (n : ℕ) :
    ∀ᵐ a ∂gaussianMatrixLaw n,
      ∀ (v : Fin n → ℝ), v ≠ 0 → ∀ z : ℝ,
        (Matrix.of a.curry) *ᵥ v = z • v → ∀ k : Fin n, v k ≠ 0 := by
  have hh := (gaussianMatrixLaw_absolutelyContinuous_volume n).ae_le
    (realMatrixObservation_det_ne_zero_ae_volume n)
  filter_upwards [hh] with a ha
  intro v hv z he k
  exact realMatrix_eigenvector_coordinate_ne_zero n _ k (ha k) v hv z he

#print axioms realObservationPolynomial_eval
#print axioms realObservationPolynomial_ne_zero
#print axioms realMatrixObservation_det_ne_zero_ae_volume
#print axioms realGaussian_eigenvectors_coordinates_ne_zero_ae
end SpectralRadiusUpperTail

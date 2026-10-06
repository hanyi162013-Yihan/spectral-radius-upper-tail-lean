import SpectralRadiusUpperTail.RealSchurFiniteAtlas
import SpectralRadiusUpperTail.RealSchurFiniteAtomicLebesgue
import SpectralRadiusUpperTail.RealGaussianAtomicNormalization
import SpectralRadiusUpperTail.RealGaussianFixedSchurIntegration

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix Matrix.Norms.Operator BigOperators

noncomputable def RealSchurFiniteAtlas.atomicSource {n : ℕ} (F : RealSchurFiniteAtlas n)
    (I : RealSchurFiniteCode n) (k : ℕ) : Set (RealSchurMixedTangent I.1.sizes) :=
  realSchurAtomicFlagSource I.1.sizes I.1.sizes_pos (F.marker I) (F.marker_injective I)
    (F.frames I) k I.2.2

theorem RealSchurFiniteAtlas.measurableSet_atomicSource {n : ℕ} (F : RealSchurFiniteAtlas n)
    (I : RealSchurFiniteCode n) (k : ℕ) : MeasurableSet (F.atomicSource I k) :=
  measurableSet_realSchurAtomicFlagSource I.1.sizes I.1.sizes_pos
    (F.marker I) (F.marker_injective I) (F.frames I) k I.2.2

/-- The actual iid real Gaussian matrix integral over the complete
scalar/nonreal-pair atlas. Overlaps across all shapes and spectral codes are
normalized exactly; no first-chart restriction truncates an upper fiber. -/
theorem realGaussian_lintegral_atomicAtlas
    (n : ℕ) (F : RealSchurFiniteAtlas n)
    (g : ((Fin n × Fin n) → ℝ) → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ x, g x ∂gaussianMatrixLaw n) =
      ∑ I : RealSchurFiniteCode n, ∑' k,
        ∫⁻ t in F.atomicSource I k,
          ENNReal.ofReal (realSchurMixedJacobianWeight I.1.sizes 0 t) *
            (realGaussianFixedDensity n (F.output I k t) *
              ((realSchurAtomicMultiplicity n (Matrix.of (F.output I k t).curry))⁻¹ *
                g (F.output I k t))) ∂realSchurMixedCoordinateVolume I.1.sizes := by
  classical
  rw [realGaussian_lintegral_finiteAtomic_normalized n g hg]
  apply Finset.sum_congr rfl
  intro I _
  have hC : @Measurable ((Fin n × Fin n) → ℝ) (Matrix (Fin n) (Fin n) ℝ)
      inferInstance (finiteMatrixMeasurableSpace n n ℝ)
      (fun x => Matrix.of x.curry) := by
    exact measurable_pi_lambda _ (fun i => measurable_pi_lambda _ (fun j => measurable_pi_apply (i,j)))
  have hS : MeasurableSet {x : (Fin n × Fin n) → ℝ |
      Matrix.of x.curry ∈ realSchurFiniteAtomicClass I} :=
    (measurableSet_realSchurFiniteAtomicClass I).preimage hC
  have hmeasure : gaussianMatrixLaw n =
      (volume : Measure ((Fin n × Fin n) → ℝ)).withDensity (realGaussianFixedDensity n) :=
    gaussianMatrixLaw_eq_explicitDensity n
  rw [hmeasure,setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable volume
    (measurable_realGaussianFixedDensity n) _ hS
    (Filter.Eventually.of_forall (realGaussianFixedDensity_lt_top n))]
  exact realSchurFiniteAtomic_lintegral I (F.marker I) (F.marker_injective I)
    (F.frames I) (F.covers I) (fun x => realGaussianFixedDensity n x *
      ((realSchurAtomicMultiplicity n (Matrix.of x.curry))⁻¹*g x))

#print axioms RealSchurFiniteAtlas.measurableSet_atomicSource
#print axioms realGaussian_lintegral_atomicAtlas
end SpectralRadiusUpperTail

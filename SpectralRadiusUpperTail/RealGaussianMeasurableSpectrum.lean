import SpectralRadiusUpperTail.RealGaussianActualSimpleSpectrum
import Ginibre.SchurSpectrumMeasurability
import Ginibre.SchurChamberNormalization
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory

/-- Reuse the independently audited complex Schur atlas to obtain a
measurable ordering of the eigenvalues of a real Gaussian matrix. The
construction works because the complex atlas covers every simple matrix,
while real Gaussian matrices have simple complex spectrum almost surely. -/
noncomputable def realGaussianMeasurableRawSpectrum (n : ℕ) :
    ((Fin n × Fin n) → ℝ) → Fin n → ℂ :=
  (Classical.choose (Ginibre.exists_measurable_schurCoordinateSpectrum n)) ∘
    (Ginibre.schurFlatEntryMeasurableEquiv n) ∘
      (fun x ij => (x ij : ℂ))

theorem realGaussianMeasurableRawSpectrum_measurable (n : ℕ) :
    Measurable (realGaussianMeasurableRawSpectrum n) := by
  unfold realGaussianMeasurableRawSpectrum
  have hchoice := (Classical.choose_spec
    (Ginibre.exists_measurable_schurCoordinateSpectrum n)).1
  apply hchoice.comp
  apply (Ginibre.schurFlatEntryMeasurableEquiv n).measurable.comp
  fun_prop

theorem realGaussianMeasurableRawSpectrum_eq_ae (n : ℕ) :
    ∀ᵐ x ∂gaussianMatrixLaw n,
      realGaussianMeasurableRawSpectrum n x =
        Ginibre.schurSpectrum ((Matrix.of x.curry).map Complex.ofRealHom) := by
  filter_upwards [realGaussianMatrix_charpoly_separable_ae n] with x hx
  have hsep : ((Matrix.of x.curry).map Complex.ofRealHom).charpoly.Separable := by
    rw [Matrix.charpoly_map]
    exact (Polynomial.separable_map (algebraMap ℝ ℂ)).mpr hx
  have hmem := Ginibre.entrySplit_simple_mem_iUnion_schurDisjointEntryImage
    ((Matrix.of x.curry).map Complex.ofRealHom) hsep
  have hflat : Ginibre.schurFlatEntryMeasurableEquiv n
      (fun ij => (x ij : ℂ)) =
      Ginibre.schurEntrySplit n ((Matrix.of x.curry).map Complex.ofRealHom) := by
    rw [Ginibre.schurFlatEntryMeasurableEquiv_apply]
    congr 1
  change (Classical.choose
      (Ginibre.exists_measurable_schurCoordinateSpectrum n))
      (Ginibre.schurFlatEntryMeasurableEquiv n
        (fun ij => (x ij : ℂ))) = _
  rw [hflat]
  exact ((Classical.choose_spec
    (Ginibre.exists_measurable_schurCoordinateSpectrum n)).2 hmem).trans
      (Ginibre.schurCoordinateSpectrum_entrySplit _)

#print axioms realGaussianMeasurableRawSpectrum_measurable
#print axioms realGaussianMeasurableRawSpectrum_eq_ae
end SpectralRadiusUpperTail

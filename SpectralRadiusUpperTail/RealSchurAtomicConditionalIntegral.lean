import SpectralRadiusUpperTail.RealSchurAtomicNativeRotation
import SpectralRadiusUpperTail.RealSchurJointGapDisintegration
import SpectralRadiusUpperTail.RealSchurAtomicSpectralWeight
import SpectralRadiusUpperTail.SchurGapPositiveSupport

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped Matrix ENNReal BigOperators

theorem realSchurNativeGapProduct_positive
    {m : ℕ} (s : Fin m → ℕ) (n : ℝ) (hn : 0 < n) (u : Fin m → ℝ)
    (hu : ∀ i, s i=2 → 0 < u i) :
    ∀ᵐ g ∂Measure.pi (fun i => realSchurNativeGapLaw (s i) n (u i)),
      ∀ i, s i=2 → 0 < g i := by
  let : ∀ i, IsProbabilityMeasure (realSchurNativeGapLaw (s i) n (u i)) :=
    fun i => realSchurNativeGapLaw_probability (s i) n (u i) hn (hu i)
  apply ae_all_iff.mpr
  intro i
  have hh : ∀ᵐ g ∂realSchurNativeGapLaw (s i) n (u i), s i=2 → 0 < g := by
    by_cases hi : s i=2
    · simp only [realSchurNativeGapLaw,hi,ite_true,true_implies]
      exact schurSquaredGapLaw_positive n (Real.sqrt (u i)) hn
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (hi h))
  exact (Measure.quasiMeasurePreserving_eval (fun j => realSchurNativeGapLaw (s j) n (u j)) i).ae hh

theorem realSchurAtomicNativeCore_coordinates_measurable
    {n : ℕ} (F : RealSchurFiniteAtlas n) (I : RealSchurFiniteCode n) (k : ℕ)
    (H : Matrix (RealSchurMixedCoord I.1.sizes) (RealSchurMixedCoord I.1.sizes) ℝ → ℝ≥0∞)
    (hH : Measurable H) :
    Measurable (fun v : Fin I.1.blockCount → ℝ × (ℝ × ℝ) =>
      realSchurAtomicNativeCore F I k H (fun i => realSchurNativeCanonicalEntries (I.1.sizes i) (v i))) := by
  apply (realSchurAtomicNativeCore_measurable F I k H hH).comp
  exact measurable_pi_lambda _ (fun i =>
    (realSchurNativeCanonicalEntries_measurable (I.1.sizes i)).comp (measurable_pi_apply i))

/-- All actual atlas weights are outside the independent gap integral.
The remaining inner observable is the full strict-upper Gaussian
integral of the canonical native block matrix. -/
theorem realSchurAtomicNativeCore_conditional_lintegral
    {n : ℕ} (F : RealSchurFiniteAtlas n) (I : RealSchurFiniteCode n) (k : ℕ)
    (H : Matrix (RealSchurMixedCoord I.1.sizes) (RealSchurMixedCoord I.1.sizes) ℝ → ℝ≥0∞)
    (hH : Measurable H) :
    (∫⁻ v : Fin I.1.blockCount → ℝ × (ℝ × ℝ),
      realSchurAtomicNativeCore F I k H
        (fun i => realSchurNativeCanonicalEntries (I.1.sizes i) (v i))
      ∂Measure.pi (fun i => realSchurNativeSpectralMeasure (I.1.sizes i) 1)) =
    ∫⁻ x : Fin I.1.blockCount → ℝ, ∫⁻ u,
      ENNReal.ofReal (∏ i : Fin I.1.blockCount, realSchurNativeSpectralFactor (I.1.sizes i) 1 (x i) (u i))*
        ((∏ i : Fin I.1.blockCount, realSchurNativeGapNormalizer (I.1.sizes i) 1 (u i))*
          (realSchurAtomicSpectralWeight F I k (realSchurCanonicalDiagonal I.1.sizes x u (fun _ => 1))*
            ∫⁻ g, realSchurGaussianUpperIntegral I.1.sizes H (realSchurCanonicalDiagonal I.1.sizes x u g)
              ∂Measure.pi (fun i => realSchurNativeGapLaw (I.1.sizes i) 1 (u i))))
      ∂Measure.pi (fun i => realSchurNativeAuxiliaryBase (I.1.sizes i)) := by
  rw [realSchurNativeSpectralProduct_disintegration I.1.sizes I.1.sizes_small 1 (by norm_num)
    (fun v => realSchurAtomicNativeCore F I k H
      (fun i => realSchurNativeCanonicalEntries (I.1.sizes i) (v i)))
    (realSchurAtomicNativeCore_coordinates_measurable F I k H hH)]
  apply lintegral_congr
  intro x
  apply lintegral_congr_ae
  filter_upwards [realSchurNativeAuxiliaryProduct_positive I.1.sizes] with u hu
  congr 2
  have he : (fun g : Fin I.1.blockCount → ℝ =>
      realSchurAtomicNativeCore F I k H
        (fun i => realSchurNativeCanonicalEntries (I.1.sizes i) (x i,u i,g i))) =ᵐ[
        Measure.pi (fun i => realSchurNativeGapLaw (I.1.sizes i) 1 (u i))]
      (fun g => realSchurAtomicSpectralWeight F I k
        (realSchurCanonicalDiagonal I.1.sizes x u (fun _ => 1))*
          realSchurGaussianUpperIntegral I.1.sizes H (realSchurCanonicalDiagonal I.1.sizes x u g)) := by
    filter_upwards [realSchurNativeGapProduct_positive I.1.sizes 1 (by norm_num) u hu] with g hg
    change realSchurAtomicCoreWeight F I k H (realSchurCanonicalDiagonal I.1.sizes x u g)=_
    rw [realSchurAtomicCoreWeight_eq_spectral_mul,
      realSchurAtomicSpectralWeight_gap_independent F I k x u g (fun _ => 1) hu hg (by intro i hi; norm_num)]
  rw [lintegral_congr_ae he]
  apply lintegral_const_mul
  exact (realSchurGaussianUpperIntegral_measurable I.1.sizes H hH).comp
    (realSchurCanonicalDiagonal_continuous_gap I.1.sizes x u).measurable

#print axioms realSchurNativeGapProduct_positive
#print axioms realSchurAtomicNativeCore_coordinates_measurable
#print axioms realSchurAtomicNativeCore_conditional_lintegral
end SpectralRadiusUpperTail

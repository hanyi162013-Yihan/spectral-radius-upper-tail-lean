import SpectralRadiusUpperTail.RealSchurAtomicGapIndependence
import SpectralRadiusUpperTail.RealSchurAtomicCoreWeight

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped Matrix ENNReal

/-- All non-Gaussian diagonal weights in the actual atlas; unlike the
core observable this contains no strictly-upper integral. -/
noncomputable def realSchurAtomicSpectralWeight
    {n : ℕ} (F : RealSchurFiniteAtlas n) (I : RealSchurFiniteCode n) (k : ℕ)
    (d : RealSchurMixedDiagonalEntry I.1.sizes → ℝ) : ℝ≥0∞ :=
  (realSchurAtomicDiagonalSource I.1.sizes I.2.2).indicator
    (fun d => ENNReal.ofReal (realSchurMixedDiagonalGapWeight I.1.sizes d)*
      realSchurAtomicDiagonalMultiplicityWeight F I k d) d

theorem realSchurAtomicSpectralWeight_measurable
    {n : ℕ} (F : RealSchurFiniteAtlas n) (I : RealSchurFiniteCode n) (k : ℕ) :
    Measurable (realSchurAtomicSpectralWeight F I k) :=
  (((realSchurMixedDiagonalGapWeight_continuous I.1.sizes).measurable.ennreal_ofReal).mul
    (realSchurAtomicDiagonalMultiplicityWeight_measurable F I k)).indicator
      (measurableSet_realSchurAtomicDiagonalSource I.1.sizes I.2.2)

theorem realSchurAtomicCoreWeight_eq_spectral_mul
    {n : ℕ} (F : RealSchurFiniteAtlas n) (I : RealSchurFiniteCode n) (k : ℕ)
    (H : Matrix (RealSchurMixedCoord I.1.sizes) (RealSchurMixedCoord I.1.sizes) ℝ → ℝ≥0∞)
    (d : RealSchurMixedDiagonalEntry I.1.sizes → ℝ) :
    realSchurAtomicCoreWeight F I k H d =
      realSchurAtomicSpectralWeight F I k d*realSchurGaussianUpperIntegral I.1.sizes H d := by
  classical
  by_cases hd : d ∈ realSchurAtomicDiagonalSource I.1.sizes I.2.2 <;>
    simp [realSchurAtomicCoreWeight,realSchurAtomicSpectralWeight,hd]

/-- The entire remaining atlas weight depends on the eigenvalue data,
not the positive gaps inside the nonreal pair blocks. -/
theorem realSchurAtomicSpectralWeight_gap_independent
    {n : ℕ} (F : RealSchurFiniteAtlas n) (I : RealSchurFiniteCode n) (k : ℕ)
    (x u a b : Fin I.1.blockCount → ℝ)
    (hu : ∀ i, I.1.sizes i=2 → 0 < u i)
    (ha : ∀ i, I.1.sizes i=2 → 0 < a i)
    (hb : ∀ i, I.1.sizes i=2 → 0 < b i) :
    realSchurAtomicSpectralWeight F I k (realSchurCanonicalDiagonal I.1.sizes x u a)=
      realSchurAtomicSpectralWeight F I k (realSchurCanonicalDiagonal I.1.sizes x u b) := by
  classical
  have hp := realSchurCanonicalDiagonal_native_charpoly_gap I.1.sizes I.1.sizes_small x u a b hu ha hb
  have hS := realSchurAtomicDiagonalSource_iff_of_polynomials I.1.sizes I.1.sizes_pos I.2.2 _ _ hp
  have hJ := realSchurMixedDiagonalGapWeight_eq_of_polynomials I.1.sizes I.1.sizes_small _ _ hp
  by_cases hd : realSchurCanonicalDiagonal I.1.sizes x u a ∈
      realSchurAtomicDiagonalSource I.1.sizes I.2.2
  · have he := hS.mp hd
    simp only [realSchurAtomicSpectralWeight,Set.indicator_of_mem hd,Set.indicator_of_mem he,hJ,
      realSchurAtomicMultiplicityWeight_gap_independent F I k x u a b hu ha hb hd.1.1]
  · have he := mt hS.mpr hd
    simp only [realSchurAtomicSpectralWeight,Set.indicator_of_notMem hd,Set.indicator_of_notMem he]

#print axioms realSchurAtomicSpectralWeight_measurable
#print axioms realSchurAtomicCoreWeight_eq_spectral_mul
#print axioms realSchurAtomicSpectralWeight_gap_independent
end SpectralRadiusUpperTail

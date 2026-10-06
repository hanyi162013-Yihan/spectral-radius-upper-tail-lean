import SpectralRadiusUpperTail.RealSchurAtomicCoreWeight
import SpectralRadiusUpperTail.RealSchurNativeGaussianCoordinates

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped Matrix ENNReal

noncomputable def realSchurAtomicNativeCore
    {n : ℕ} (F : RealSchurFiniteAtlas n) (I : RealSchurFiniteCode n) (k : ℕ)
    (H : Matrix (RealSchurMixedCoord I.1.sizes) (RealSchurMixedCoord I.1.sizes) ℝ → ℝ≥0∞)
    (D : (i : Fin I.1.blockCount) → (Fin (I.1.sizes i) × Fin (I.1.sizes i)) → ℝ) : ℝ≥0∞ :=
  realSchurAtomicCoreWeight F I k H ((realSchurMixedDiagonalProductEquiv I.1.sizes).symm D)

theorem realSchurAtomicNativeCore_measurable
    {n : ℕ} (F : RealSchurFiniteAtlas n) (I : RealSchurFiniteCode n) (k : ℕ)
    (H : Matrix (RealSchurMixedCoord I.1.sizes) (RealSchurMixedCoord I.1.sizes) ℝ → ℝ≥0∞)
    (hH : Measurable H) : Measurable (realSchurAtomicNativeCore F I k H) :=
  (realSchurAtomicCoreWeight_measurable F I k H hH).comp
    (realSchurMixedDiagonalProductEquiv I.1.sizes).symm.measurable

theorem realSchurMixedDiagonalProduct_symm_conjugation
    {m : ℕ} (s : Fin m → ℕ)
    (Q : (i : Fin m) → Matrix (Fin (s i)) (Fin (s i)) ℝ)
    (D : (i : Fin m) → (Fin (s i) × Fin (s i)) → ℝ) :
    (realSchurMixedDiagonalProductEquiv s).symm
      (fun i ab => (Q i*Matrix.of (D i).curry*(Q i)ᵀ) ab.1 ab.2) =
        realSchurMixedDiagonalConjugation s (Matrix.blockDiagonal' Q)
          ((realSchurMixedDiagonalProductEquiv s).symm D) := by
  apply (realSchurMixedDiagonalProductEquiv s).injective
  rw [MeasurableEquiv.apply_symm_apply]
  funext i ab
  have hh := realSchurMixedDiagonalProduct_conjugation s Q
    ((realSchurMixedDiagonalProductEquiv s).symm D) i
  rw [MeasurableEquiv.apply_symm_apply] at hh
  exact (congrArg (fun A : Matrix (Fin (s i)) (Fin (s i)) ℝ => A ab.1 ab.2) hh).symm

theorem realSchurAtomicNativeCore_rotation
    {n : ℕ} (F : RealSchurFiniteAtlas n) (I : RealSchurFiniteCode n) (k : ℕ)
    (H : Matrix (RealSchurMixedCoord I.1.sizes) (RealSchurMixedCoord I.1.sizes) ℝ → ℝ≥0∞)
    (hH : Measurable H)
    (hInv : ∀ W : Matrix (RealSchurMixedCoord I.1.sizes) (RealSchurMixedCoord I.1.sizes) ℝ,
      Wᵀ*W=1 → ∀ A, H (W*A*Wᵀ)=H A)
    (Q : (i : Fin I.1.blockCount) → Matrix (Fin (I.1.sizes i)) (Fin (I.1.sizes i)) ℝ)
    (hQ : ∀ i, (Q i)ᵀ*Q i=1)
    (D : (i : Fin I.1.blockCount) → (Fin (I.1.sizes i) × Fin (I.1.sizes i)) → ℝ) :
    realSchurAtomicNativeCore F I k H (fun i ab => (Q i*Matrix.of (D i).curry*(Q i)ᵀ) ab.1 ab.2)=
      realSchurAtomicNativeCore F I k H D := by
  unfold realSchurAtomicNativeCore
  rw [realSchurMixedDiagonalProduct_symm_conjugation]
  exact realSchurAtomicCoreWeight_block_rotation F I k H hH hInv Q hQ _

theorem realSchurAtomicDiagonalSource_native_mem
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (code : Fin m → Fin (Fintype.card (RealSchurMixedCoord s)) → Bool)
    (d : RealSchurMixedDiagonalEntry s → ℝ)
    (hd : d ∈ realSchurAtomicDiagonalSource s code) (i : Fin m) :
    realSchurMixedDiagonalProductEquiv s d i ∈ realSchurNativeAtomicEntrySet (s i) := by
  have ht := hd.2
  rw [← hd.1.2] at ht
  have hb := (realSchurMixedAtomicBlocks_iff_codeTest s hs _
    (realSchurMixedUpperEntryJoin_lower_zero s d 0) hd.1.1).mpr ht
  apply realSchurNativeAtomicEntrySet_of_noRealRoot
  intro hi x
  have hh := hb i hi x
  rw [realSchurMixedDiagonalProductEquiv_nativeBlock] at hh
  exact hh

/-- The actual atomic core already vanishes outside the product of the
native scalar/nonreal-pair domains, so restricting each block loses no mass. -/
theorem realSchurAtomicNativeCore_support
    {n : ℕ} (F : RealSchurFiniteAtlas n) (I : RealSchurFiniteCode n) (k : ℕ)
    (H : Matrix (RealSchurMixedCoord I.1.sizes) (RealSchurMixedCoord I.1.sizes) ℝ → ℝ≥0∞) :
    Function.support (realSchurAtomicNativeCore F I k H) ⊆
      Set.pi Set.univ (fun i => realSchurNativeAtomicEntrySet (I.1.sizes i)) := by
  intro D hD i _
  have hd : (realSchurMixedDiagonalProductEquiv I.1.sizes).symm D ∈
      realSchurAtomicDiagonalSource I.1.sizes I.2.2 := by
    by_contra h
    exact hD (by simp [realSchurAtomicNativeCore,realSchurAtomicCoreWeight,Set.indicator_of_notMem h])
  simpa only [MeasurableEquiv.apply_symm_apply] using
    realSchurAtomicDiagonalSource_native_mem I.1.sizes I.1.sizes_pos I.2.2 _ hd i

#print axioms realSchurAtomicNativeCore_measurable
#print axioms realSchurMixedDiagonalProduct_symm_conjugation
#print axioms realSchurAtomicNativeCore_rotation
#print axioms realSchurAtomicDiagonalSource_native_mem
#print axioms realSchurAtomicNativeCore_support
end SpectralRadiusUpperTail

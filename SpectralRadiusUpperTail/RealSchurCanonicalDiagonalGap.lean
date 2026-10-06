import SpectralRadiusUpperTail.RealSchurNativeGapPolynomial
import SpectralRadiusUpperTail.RealSchurMixedDiagonalProductIntegral
import SpectralRadiusUpperTail.RealSchurAtomicDiagonalSpectralDependence

namespace SpectralRadiusUpperTail
open scoped Matrix

theorem realSchurMixedDiagonalProduct_symm_continuous
    {m : ℕ} (s : Fin m → ℕ) : Continuous (realSchurMixedDiagonalProductEquiv s).symm := by
  apply continuous_pi
  intro p
  have he (D : (i : Fin m) → (Fin (s i) × Fin (s i)) → ℝ) :
      (realSchurMixedDiagonalProductEquiv s).symm D p=
        D ((realSchurMixedDiagonalIndexEquiv s).symm p).1 ((realSchurMixedDiagonalIndexEquiv s).symm p).2 := by
    have hh := congrArg (fun V : (i : Fin m) → (Fin (s i) × Fin (s i)) → ℝ =>
      V ((realSchurMixedDiagonalIndexEquiv s).symm p).1 ((realSchurMixedDiagonalIndexEquiv s).symm p).2)
        ((realSchurMixedDiagonalProductEquiv s).apply_symm_apply D)
    change (realSchurMixedDiagonalProductEquiv s).symm D
      (realSchurMixedDiagonalIndexEquiv s ((realSchurMixedDiagonalIndexEquiv s).symm p))=_ at hh
    simpa only [Equiv.apply_symm_apply] using hh
  simp_rw [he]
  fun_prop

noncomputable def realSchurCanonicalDiagonal {m : ℕ} (s : Fin m → ℕ)
    (x u g : Fin m → ℝ) : RealSchurMixedDiagonalEntry s → ℝ :=
  (realSchurMixedDiagonalProductEquiv s).symm
    (fun i => realSchurNativeCanonicalEntries (s i) (x i,u i,g i))

theorem realSchurCanonicalDiagonal_continuous_gap {m : ℕ} (s : Fin m → ℕ)
    (x u : Fin m → ℝ) : Continuous (realSchurCanonicalDiagonal s x u) := by
  apply (realSchurMixedDiagonalProduct_symm_continuous s).comp
  apply continuous_pi
  intro i
  apply (realSchurNativeCanonicalEntries_continuous (s i)).comp
  fun_prop

theorem realSchurCanonicalDiagonal_native_charpoly_gap
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, s i=1 ∨ s i=2)
    (x u a b : Fin m → ℝ) (hu : ∀ i, s i=2 → 0 < u i)
    (ha : ∀ i, s i=2 → 0 < a i) (hb : ∀ i, s i=2 → 0 < b i) (i : Fin m) :
    (realSchurMixedDiagonalMatrix s
      (realSchurMixedUpperEntryJoin s (realSchurCanonicalDiagonal s x u a) 0) i).charpoly=
    (realSchurMixedDiagonalMatrix s
      (realSchurMixedUpperEntryJoin s (realSchurCanonicalDiagonal s x u b) 0) i).charpoly := by
  simp only [realSchurMixedDiagonalProductEquiv_nativeBlock,realSchurCanonicalDiagonal,
    MeasurableEquiv.apply_symm_apply]
  exact realSchurNativeCanonicalEntries_charpoly_gap (s i) (hs i) (x i) (u i) (a i) (b i)
    (hu i) (ha i) (hb i)

theorem realSchurCanonicalDiagonal_charpoly_gap
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i) (hsmall : ∀ i, s i=1 ∨ s i=2)
    (x u a b : Fin m → ℝ) (hu : ∀ i, s i=2 → 0 < u i)
    (ha : ∀ i, s i=2 → 0 < a i) (hb : ∀ i, s i=2 → 0 < b i) :
    (realSchurMixedUpperEntryJoin s (realSchurCanonicalDiagonal s x u a) 0).charpoly=
      (realSchurMixedUpperEntryJoin s (realSchurCanonicalDiagonal s x u b) 0).charpoly :=
  realSchurMixed_charpoly_eq_of_diagonal_polynomials s hs _ _
    (realSchurMixedUpperEntryJoin_lower_zero s _ 0) (realSchurMixedUpperEntryJoin_lower_zero s _ 0)
    (realSchurCanonicalDiagonal_native_charpoly_gap s hsmall x u a b hu ha hb)

#print axioms realSchurMixedDiagonalProduct_symm_continuous
#print axioms realSchurCanonicalDiagonal_continuous_gap
#print axioms realSchurCanonicalDiagonal_native_charpoly_gap
#print axioms realSchurCanonicalDiagonal_charpoly_gap
end SpectralRadiusUpperTail

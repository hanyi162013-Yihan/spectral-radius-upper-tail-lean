import SpectralRadiusUpperTail.RealSchurMixedFlagUnique
import SpectralRadiusUpperTail.RealSchurMixedSpectralCodeMeasurable
import SpectralRadiusUpperTail.RealMatrixSimpleSpectrumOpen
import SpectralRadiusUpperTail.RealSchurMixedRegularGaussianIntegration

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Operator

/-- The source of one angle patch and one finite spectral class.
The simple-spectrum and code conditions depend only on diagonal blocks. -/
noncomputable def realSchurMixedFlagCodedSource
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (c : Fin m → ℝ) (hc : Function.Injective c)
    (R : ℕ → RealSchurMixedOrthogonalFrame s) (k : ℕ)
    (code : Fin m → Fin (Fintype.card (RealSchurMixedCoord s)) → Bool) :
    Set (RealSchurMixedTangent s) :=
  {x | x.1 ∈ realSchurMixedFlagAnglePatch s hs c hc R k ∧
    x.2.val.charpoly.Separable ∧ realSchurMixedSpectralCode s x.2.val=code}

theorem measurableSet_realSchurMixedFlagCodedSource
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (c : Fin m → ℝ) (hc : Function.Injective c)
    (R : ℕ → RealSchurMixedOrthogonalFrame s) (k : ℕ)
    (code : Fin m → Fin (Fintype.card (RealSchurMixedCoord s)) → Bool) :
    MeasurableSet (realSchurMixedFlagCodedSource s hs c hc R k code) := by
  have hupper : Continuous (fun x : RealSchurMixedTangent s => x.2.val) :=
    continuous_subtype_val.comp continuous_snd
  exact ((measurableSet_realSchurMixedFlagAnglePatch s hs c hc R k).preimage
    continuous_fst.measurable).inter
      (((isOpen_realMatrix_charpoly_separable _).preimage hupper).measurableSet.inter
        (measurableSet_eq_fun ((realSchurMixedSpectralCode_measurable s).comp hupper.measurable)
          measurable_const))

theorem realSchurMixedFlagCodedSource_unique
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (c : Fin m → ℝ) (hc : Function.Injective c)
    (R : ℕ → RealSchurMixedOrthogonalFrame s) (k l : ℕ)
    (code : Fin m → Fin (Fintype.card (RealSchurMixedCoord s)) → Bool)
    (x y : RealSchurMixedTangent s)
    (hx : x ∈ realSchurMixedFlagCodedSource s hs c hc R k code)
    (hy : y ∈ realSchurMixedFlagCodedSource s hs c hc R l code)
    (heq : realSchurMixedRotatedEntryCoordinates s 0 (R k).val (R k).property x =
      realSchurMixedRotatedEntryCoordinates s 0 (R l).val (R l).property y) :
    k=l ∧ x=y := by
  have he : ((R k).val*realSchurMixedAngularFrame s x.1)*x.2.val*
      ((R k).val*realSchurMixedAngularFrame s x.1)ᵀ =
      ((R l).val*realSchurMixedAngularFrame s y.1)*y.2.val*
        ((R l).val*realSchurMixedAngularFrame s y.1)ᵀ := by
    rw [realSchurMixedRotatedEntryCoordinates_eq,
      realSchurMixedRotatedEntryCoordinates_eq] at heq
    have h := (realSchurMixedEntryEquiv s).injective heq
    simpa only [realSchurMixedExpCoordinates_eq_conjugation, zero_add,
      Matrix.transpose_mul, Matrix.mul_assoc] using h
  have hpoly : x.2.val.charpoly=y.2.val.charpoly := by
    have h := congrArg Matrix.charpoly he
    simpa only [realMatrixOrthogonalConjugation_charpoly _ _ _
      (realSchurMixed_rotatedFrame_orthogonal s (R k) x.1),
      realMatrixOrthogonalConjugation_charpoly _ _ _
      (realSchurMixed_rotatedFrame_orthogonal s (R l) y.1)] using h
  have hdiag (a : Fin m) :
      (y.2.val.toSquareBlock (fun i : RealSchurMixedCoord s => i.1) a).charpoly =
        (x.2.val.toSquareBlock (fun i : RealSchurMixedCoord s => i.1) a).charpoly := by
    rw [realSchurMixedDiagonalMatrix_charpoly, realSchurMixedDiagonalMatrix_charpoly]
    exact (realSchurMixed_diagonal_charpoly_eq_of_code s hs x.2.val y.2.val
      x.2.property y.2.property hx.2.1 hpoly (hx.2.2.trans hy.2.2.symm) a).symm
  obtain ⟨hkl,hangle,hupper⟩ := realSchurMixedFlag_representation_unique s hs c hc R k l
    x.1 y.1 hx.1 hy.1 x.2.val y.2.val
    ((realSchurMixed_blockTriangular_iff_lower_zero s x.2.val).mpr x.2.property)
    ((realSchurMixed_blockTriangular_iff_lower_zero s y.2.val).mpr y.2.property)
    hx.2.1 hdiag he
  exact ⟨hkl,Prod.ext hangle (Subtype.ext hupper)⟩

#print axioms measurableSet_realSchurMixedFlagCodedSource
#print axioms realSchurMixedFlagCodedSource_unique
end SpectralRadiusUpperTail

import SpectralRadiusUpperTail.RealPolynomialNonrealLabelTest
import SpectralRadiusUpperTail.RealSchurMixedSpectralCodeMeasurable

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Operator

def realSchurMixedAtomicBlocks {m : ℕ} (s : Fin m → ℕ)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ) : Prop :=
  ∀ a, s a=2 → ∀ x : ℝ, (realSchurMixedDiagonalMatrix s T a).charpoly.eval x ≠ 0

/-- A finite test that two-dimensional blocks contain only nonreal
canonical eigenvalue labels. This is measurable in the ambient matrix. -/
def realSchurAtomicCodeTest {m : ℕ} (s : Fin m → ℕ)
    (code : Fin m → Fin (Fintype.card (RealSchurMixedCoord s)) → Bool)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ) : Prop :=
  ∀ a, s a=2 → ∀ i, code a i=true → (realSchurMixedCanonicalSpectrum s T i).im ≠ 0

theorem realSchurMixedAtomicBlocks_iff_codeTest
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hT : realSchurMixedLowerProjection s T=0) (hsep : T.charpoly.Separable) :
    realSchurMixedAtomicBlocks s T ↔ realSchurAtomicCodeTest s (realSchurMixedSpectralCode s T) T := by
  have htest (a : Fin m) := realPolynomial_noRealRoot_iff_label_tests T.charpoly
    (realSchurMixedDiagonalMatrix s T a).charpoly
    (realSchurMixedDiagonalMatrix_charpoly_dvd s hs T hT a)
    (realSchurMixedCanonicalSpectrum s T) (realSchurMixedCanonicalSpectrum_covers s T hsep)
  simp only [realSchurMixedAtomicBlocks,realSchurAtomicCodeTest,realSchurMixedSpectralCode,
    decide_eq_true_eq]
  exact forall_congr' (fun a => imp_congr_right (fun _ => htest a))

theorem measurableSet_realSchurAtomicCodeTest
    {m : ℕ} (s : Fin m → ℕ)
    (code : Fin m → Fin (Fintype.card (RealSchurMixedCoord s)) → Bool) :
    MeasurableSet {T | realSchurAtomicCodeTest s code T} := by
  have hlabel (i : Fin (Fintype.card (RealSchurMixedCoord s))) :
      MeasurableSet {T | (realSchurMixedCanonicalSpectrum s T i).im ≠ 0} :=
    (measurableSet_eq_fun
      (Complex.continuous_im.measurable.comp
        ((measurable_pi_apply i).comp (realSchurMixedCanonicalSpectrum_measurable s)))
      measurable_const).compl
  unfold realSchurAtomicCodeTest
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter (fun a => MeasurableSet.iInter (fun _ : s a=2 =>
    MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun _ : code a i=true => hlabel i))))

theorem realSchurAtomicCodeTest_iff_of_charpoly
    {m : ℕ} (s : Fin m → ℕ)
    (code : Fin m → Fin (Fintype.card (RealSchurMixedCoord s)) → Bool)
    (T U : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hT : T.charpoly.Separable) (hU : U.charpoly.Separable) (hpoly : T.charpoly=U.charpoly) :
    realSchurAtomicCodeTest s code T ↔ realSchurAtomicCodeTest s code U := by
  unfold realSchurAtomicCodeTest
  rw [realSchurMixedCanonicalSpectrum_eq_of_charpoly s T U hT hU hpoly]

#print axioms realSchurMixedAtomicBlocks_iff_codeTest
#print axioms measurableSet_realSchurAtomicCodeTest
#print axioms realSchurAtomicCodeTest_iff_of_charpoly
end SpectralRadiusUpperTail

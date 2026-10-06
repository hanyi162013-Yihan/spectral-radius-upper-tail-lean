import SpectralRadiusUpperTail.RealPairSpectralGapCoordinates
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

namespace SpectralRadiusUpperTail
open scoped Matrix ENNReal

noncomputable def realPairCanonicalEntries (A : (Fin 2 × Fin 2) → ℝ) : (Fin 2 × Fin 2) → ℝ :=
  realPairGapBlockEntries (realPairSpectralGapCoordinates A).1 (realPairSpectralGapCoordinates A).2

theorem realPairFromCoordinates_polar (q r : ℝ) (hr : 0 ≤ r) :
    realSchurPairFromCoordinates (q^2-r^2) (4*r^2)=(|q|+r,|q|-r) := by
  unfold realSchurPairFromCoordinates
  rw [show 4*r^2+4*(q^2-r^2)=(2*q)^2 by ring,
    show 4*r^2=(2*r)^2 by ring]
  simp only [Real.sqrt_sq_eq_abs,abs_mul,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),abs_of_nonneg hr]
  apply Prod.ext <;> dsimp <;> ring

theorem realPairInvariant_cartesian_canonical
    (g : ((Fin 2 × Fin 2) → ℝ) → ℝ≥0∞) (h : RealPairOrthogonalInvariant g)
    (x a p q : ℝ) :
    g (fun ij => realPairCartesianMatrix x a p q ij.1 ij.2)=
      g (realPairCanonicalEntries (fun ij => realPairCartesianMatrix x a p q ij.1 ij.2)) := by
  let z : ℂ := ⟨a,p⟩
  let r : ℝ := ‖z‖
  have hr : 0 ≤ r := norm_nonneg _
  have hr2 : r^2=a^2+p^2 := by
    dsimp only [r,z]
    rw [← Complex.normSq_eq_norm_sq]
    change a*a+p*p=a^2+p^2
    ring
  have ha : r*Real.cos z.arg=a := Complex.norm_mul_cos_arg z
  have hp : r*Real.sin z.arg=p := Complex.norm_mul_sin_arg z
  have hpol := realPairInvariant_polar_value g h z.arg x r q
  rw [ha,hp] at hpol
  have hsign : g (fun ij => realSchurBlock x (q+r) (q-r) ij.1 ij.2)=
      g (fun ij => realSchurBlock x (|q|+r) (|q|-r) ij.1 ij.2) := by
    by_cases hq : 0 ≤ q
    · rw [abs_of_nonneg hq]
    · rw [abs_of_neg (lt_of_not_ge hq)]
      exact (realPairInvariant_skew_neg g h x r q).symm
  have hc : realPairCanonicalEntries (fun ij => realPairCartesianMatrix x a p q ij.1 ij.2) =
      (fun ij => realSchurBlock x (|q|+r) (|q|-r) ij.1 ij.2) := by
    unfold realPairCanonicalEntries
    rw [realPairSpectralGapCoordinates_cartesian]
    change realPairGapBlockEntries x (q^2-(a^2+p^2),4*(a^2+p^2))=_
    rw [← hr2]
    change (fun ij : Fin 2 × Fin 2 => realSchurBlock x
      (realSchurPairFromCoordinates (q^2-r^2) (4*r^2)).1
      (realSchurPairFromCoordinates (q^2-r^2) (4*r^2)).2 ij.1 ij.2)=_
    rw [realPairFromCoordinates_polar q r hr]
  exact hpol.trans (hsign.trans (congrArg g hc.symm))

/-- Every orthogonally invariant two-by-two observable is a function of
the explicit real-part, squared-imaginary-part and squared-gap coordinates.
No measurable choice of a conjugating frame is needed. -/
theorem realPairInvariant_canonical_value
    (g : ((Fin 2 × Fin 2) → ℝ) → ℝ≥0∞) (h : RealPairOrthogonalInvariant g)
    (A : (Fin 2 × Fin 2) → ℝ) : g A=g (realPairCanonicalEntries A) := by
  have hh := realPairInvariant_cartesian_canonical g h
    ((A (0,0)+A (1,1))/2) ((A (0,0)-A (1,1))/2)
    ((A (0,1)+A (1,0))/2) ((A (0,1)-A (1,0))/2)
  have he : (fun ij : Fin 2 × Fin 2 =>
      realPairCartesianMatrix ((A (0,0)+A (1,1))/2) ((A (0,0)-A (1,1))/2)
        ((A (0,1)+A (1,0))/2) ((A (0,1)-A (1,0))/2) ij.1 ij.2)=A :=
    congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => fun ij : Fin 2 × Fin 2 => M ij.1 ij.2)
      (realPairCartesianMatrix_reconstruct (Matrix.of A.curry))
  rw [he] at hh
  exact hh

#print axioms realPairFromCoordinates_polar
#print axioms realPairInvariant_cartesian_canonical
#print axioms realPairInvariant_canonical_value
end SpectralRadiusUpperTail

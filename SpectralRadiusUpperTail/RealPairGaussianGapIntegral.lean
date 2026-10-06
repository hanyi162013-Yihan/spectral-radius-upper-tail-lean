import SpectralRadiusUpperTail.RealPairNonrealGapIntegral

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix Matrix.Norms.Frobenius

noncomputable def realPairGaussianWeight (n : ℝ) (A : (Fin 2 × Fin 2) → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(n/2)*(∑ ij, (A ij)^2)))

theorem realPairGaussianWeight_measurable (n : ℝ) : Measurable (realPairGaussianWeight n) := by
  unfold realPairGaussianWeight
  fun_prop

theorem realPairGaussianWeight_invariant (n : ℝ) : RealPairOrthogonalInvariant (realPairGaussianWeight n) := by
  intro Q hQ A
  have hU : Q ∈ Matrix.unitaryGroup (Fin 2) ℝ := by
    rw [Matrix.mem_unitaryGroup_iff',Matrix.star_eq_conjTranspose]
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hQ
  have hn := matrix_unitary_conjugation_frobenius_sq A (⟨Q,hU⟩ : Matrix.unitaryGroup (Fin 2) ℝ)
  simp only [Matrix.conjTranspose_eq_transpose_of_trivial,real_frobenius_norm_sq] at hn
  have hsum : (∑ ij : Fin 2 × Fin 2, ((Q*A*Qᵀ) ij.1 ij.2)^2) =
      ∑ ij : Fin 2 × Fin 2, (A ij.1 ij.2)^2 := by
    simpa only [Fintype.sum_prod_type] using hn
  unfold realPairGaussianWeight
  rw [hsum]

theorem realPairGaussianWeight_gap (n x u s : ℝ) (hu : 0 < u) (hs : 0 < s) :
    realPairGaussianWeight n (realPairGapBlockEntries x (u,s)) =
      ENNReal.ofReal (Real.exp (-n*(x^2+u)) * Real.exp (-(n/2)*s)) := by
  let p := realSchurPairFromCoordinates u s
  have hc := realSchur_pair_chart_forward u s hu hs
  have h₁ : p.1*p.2=u := congrArg Prod.fst hc
  have h₂ : (p.1-p.2)^2=s := congrArg Prod.snd hc
  have he : p.1^2+p.2^2=s+2*u := by nlinarith
  have hsum : (∑ ij : Fin 2 × Fin 2, (realPairGapBlockEntries x (u,s) ij)^2) =
      2*x^2+(s+2*u) := by
    calc
      _ = 2*x^2+(p.1^2+p.2^2) := by
        simp [realPairGapBlockEntries,realSchurBlock,Fintype.sum_prod_type,Fin.sum_univ_two,p]
        ring
      _ = _ := by rw [he]
  unfold realPairGaussianWeight
  rw [hsum,← Real.exp_add]
  congr 2
  ring

/-- Actual four-entry Gaussian integration on the nonreal locus. The
spectral weight and the squared-gap weight are separated exactly. -/
theorem realPairGaussian_nonreal_gap_lintegral
    (n : ℝ) (H : ((Fin 2 × Fin 2) → ℝ) → ℝ≥0∞) (hH : Measurable H)
    (hInv : RealPairOrthogonalInvariant H) :
    (∫⁻ A in realPairNonrealEntrySet, realPairGaussianWeight n A * H A) =
      ENNReal.ofReal (2*Real.pi) *
        (∫⁻ x : ℝ, ∫⁻ v in realSchurPairCoordinateDomain,
          ENNReal.ofReal (Real.exp (-n*(x^2+v.1))) *
            (ENNReal.ofReal ((Real.sqrt (v.2+4*v.1))⁻¹) *
              ENNReal.ofReal (Real.exp (-(n/2)*v.2)) * H (realPairGapBlockEntries x v))) := by
  have hW : RealPairOrthogonalInvariant (fun A => realPairGaussianWeight n A * H A) := by
    intro Q hQ A
    dsimp only
    rw [realPairGaussianWeight_invariant n Q hQ A,hInv Q hQ A]
  rw [realPairInvariant_nonreal_gap_lintegral
    (fun A => realPairGaussianWeight n A * H A) ((realPairGaussianWeight_measurable n).mul hH) hW]
  congr 1
  apply lintegral_congr
  intro x
  apply setLIntegral_congr_fun realSchurPairCoordinateDomain_isOpen.measurableSet
  intro v hv
  dsimp only
  rw [realPairGaussianWeight_gap n x v.1 v.2 hv.1 hv.2,
    ENNReal.ofReal_mul (Real.exp_pos _).le]
  ac_rfl

#print axioms realPairGaussianWeight_measurable
#print axioms realPairGaussianWeight_invariant
#print axioms realPairGaussianWeight_gap
#print axioms realPairGaussian_nonreal_gap_lintegral
end SpectralRadiusUpperTail

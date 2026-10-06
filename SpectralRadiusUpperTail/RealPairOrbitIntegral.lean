import SpectralRadiusUpperTail.RealPairPolarVolume
import SpectralRadiusUpperTail.RealPairPolarRotation

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix

/-- Orthogonal invariance stated directly for functions of the four
original real entries. -/
def RealPairOrthogonalInvariant (g : ((Fin 2 × Fin 2) → ℝ) → ℝ≥0∞) : Prop :=
  ∀ Q : Matrix (Fin 2) (Fin 2) ℝ, Qᵀ*Q=1 →
    ∀ A : Matrix (Fin 2) (Fin 2) ℝ,
      g (fun ij => (Q*A*Qᵀ) ij.1 ij.2)=g (fun ij => A ij.1 ij.2)

theorem realPairInvariant_polar_value
    (g : ((Fin 2 × Fin 2) → ℝ) → ℝ≥0∞) (h : RealPairOrthogonalInvariant g)
    (φ x r q : ℝ) :
    g (fun ij => realPairCartesianMatrix x (r*Real.cos φ) (r*Real.sin φ) q ij.1 ij.2) =
      g (fun ij => realSchurBlock x (q+r) (q-r) ij.1 ij.2) := by
  simp_rw [realPairPolarMatrix_conjugate]
  exact h _ (realSchurRotation_orthogonal _) _

/-- Integration of the entire angular variable for any nonnegative
orthogonally invariant entry observable. -/
theorem realPairInvariant_orbit_lintegral
    (g : ((Fin 2 × Fin 2) → ℝ) → ℝ≥0∞) (hg : Measurable g)
    (h : RealPairOrthogonalInvariant g) :
    (∫⁻ A, g A) = ENNReal.ofReal (8*Real.pi) *
      (∫⁻ x : ℝ, ∫⁻ q : ℝ, ∫⁻ r in Set.Ioi (0 : ℝ),
        ENNReal.ofReal r * g (fun ij => realSchurBlock x (q+r) (q-r) ij.1 ij.2)) := by
  rw [realPair_polar_lintegral g hg]
  simp_rw [realPairInvariant_polar_value g h]
  simp only [lintegral_const,Measure.restrict_apply_univ,Real.volume_Ioo]
  simp_rw [lintegral_mul_const' (ENNReal.ofReal (Real.pi-(-Real.pi))) _ ENNReal.ofReal_ne_top]
  have hc : (4 : ℝ≥0∞) * ENNReal.ofReal (Real.pi-(-Real.pi)) = ENNReal.ofReal (8*Real.pi) := by
    rw [show (8*Real.pi : ℝ)=4*(Real.pi-(-Real.pi)) by ring,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),ENNReal.ofReal_ofNat]
  rw [← hc]
  ac_rfl

/-- Exchanging the two axes reverses the skew sign and leaves the same
positive polar radius. Both orientation components contribute equally. -/
theorem realPairInvariant_skew_neg
    (g : ((Fin 2 × Fin 2) → ℝ) → ℝ≥0∞) (h : RealPairOrthogonalInvariant g)
    (x r q : ℝ) :
    g (fun ij => realSchurBlock x (-q+r) (-q-r) ij.1 ij.2) =
      g (fun ij => realSchurBlock x (q+r) (q-r) ij.1 ij.2) := by
  let Q : Matrix (Fin 2) (Fin 2) ℝ := !![0,1;1,0]
  have hQ : Qᵀ*Q=1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Q,Matrix.mul_apply,Fin.sum_univ_two]
  have he : Q*realSchurBlock x (q+r) (q-r)*Qᵀ=realSchurBlock x (-q+r) (-q-r) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Q,realSchurBlock,Matrix.mul_apply,Fin.sum_univ_two] <;> ring
  have hh := h Q hQ (realSchurBlock x (q+r) (q-r))
  simpa only [he] using hh

#print axioms realPairInvariant_polar_value
#print axioms realPairInvariant_orbit_lintegral
#print axioms realPairInvariant_skew_neg
end SpectralRadiusUpperTail

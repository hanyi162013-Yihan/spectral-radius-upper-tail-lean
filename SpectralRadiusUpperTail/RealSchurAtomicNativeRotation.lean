import SpectralRadiusUpperTail.RealSchurAtomicNativeCore
import SpectralRadiusUpperTail.RealSchurNativeProductIntegral
import SpectralRadiusUpperTail.RealSchurNativeRestrictedIntegral

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped Matrix ENNReal BigOperators

theorem realSchurAtomicNativeCore_single_rotation
    {n : ℕ} (F : RealSchurFiniteAtlas n) (I : RealSchurFiniteCode n) (k : ℕ)
    (H : Matrix (RealSchurMixedCoord I.1.sizes) (RealSchurMixedCoord I.1.sizes) ℝ → ℝ≥0∞)
    (hH : Measurable H)
    (hInv : ∀ W : Matrix (RealSchurMixedCoord I.1.sizes) (RealSchurMixedCoord I.1.sizes) ℝ,
      Wᵀ*W=1 → ∀ A, H (W*A*Wᵀ)=H A)
    (D : (i : Fin I.1.blockCount) → (Fin (I.1.sizes i) × Fin (I.1.sizes i)) → ℝ)
    (i : Fin I.1.blockCount) (Q : Matrix (Fin (I.1.sizes i)) (Fin (I.1.sizes i)) ℝ)
    (hQ : Qᵀ*Q=1) :
    realSchurAtomicNativeCore F I k H
      (Function.update D i (fun ab => (Q*Matrix.of (D i).curry*Qᵀ) ab.1 ab.2))=
        realSchurAtomicNativeCore F I k H D := by
  classical
  let R : (j : Fin I.1.blockCount) → Matrix (Fin (I.1.sizes j)) (Fin (I.1.sizes j)) ℝ :=
    Function.update (fun _ => 1) i Q
  have hR : ∀ j, (R j)ᵀ*R j=1 := by
    intro j
    by_cases hj : j=i
    · subst j
      simpa [R] using hQ
    · simp [R,hj]
  have hh := realSchurAtomicNativeCore_rotation F I k H hH hInv R hR D
  have he : (fun j ab => (R j*Matrix.of (D j).curry*(R j)ᵀ) ab.1 ab.2)=
      Function.update D i (fun ab => (Q*Matrix.of (D i).curry*Qᵀ) ab.1 ab.2) := by
    funext j ab
    by_cases hj : j=i
    · subst j
      simp [R]
    · simp [R,hj]
  rw [he] at hh
  exact hh

theorem realSchurAtomicNativeCore_separate_invariant
    {n : ℕ} (F : RealSchurFiniteAtlas n) (I : RealSchurFiniteCode n) (k : ℕ)
    (H : Matrix (RealSchurMixedCoord I.1.sizes) (RealSchurMixedCoord I.1.sizes) ℝ → ℝ≥0∞)
    (hH : Measurable H)
    (hInv : ∀ W : Matrix (RealSchurMixedCoord I.1.sizes) (RealSchurMixedCoord I.1.sizes) ℝ,
      Wᵀ*W=1 → ∀ A, H (W*A*Wᵀ)=H A)
    (i : Fin I.1.blockCount)
    (D : (j : Fin I.1.blockCount) → (Fin (I.1.sizes j) × Fin (I.1.sizes j)) → ℝ)
    (Q : Matrix (Fin (I.1.sizes i)) (Fin (I.1.sizes i)) ℝ) (hQ : Qᵀ*Q=1)
    (A : Matrix (Fin (I.1.sizes i)) (Fin (I.1.sizes i)) ℝ) :
    realSchurAtomicNativeCore F I k H (Function.update D i (fun ab => (Q*A*Qᵀ) ab.1 ab.2))=
      realSchurAtomicNativeCore F I k H (Function.update D i (fun ab => A ab.1 ab.2)) := by
  have hh := realSchurAtomicNativeCore_single_rotation F I k H hH hInv
    (Function.update D i (fun ab => A ab.1 ab.2)) i Q hQ
  rw [Function.update_self,Function.update_idem] at hh
  exact hh

/-- The diagonal part of the actual atlas integral now has its full
joint native spectral/gap pushforward measure. -/
theorem realSchurAtomicNativeCore_spectral_lintegral
    {n : ℕ} (F : RealSchurFiniteAtlas n) (I : RealSchurFiniteCode n) (k : ℕ)
    (H : Matrix (RealSchurMixedCoord I.1.sizes) (RealSchurMixedCoord I.1.sizes) ℝ → ℝ≥0∞)
    (hH : Measurable H)
    (hInv : ∀ W : Matrix (RealSchurMixedCoord I.1.sizes) (RealSchurMixedCoord I.1.sizes) ℝ,
      Wᵀ*W=1 → ∀ A, H (W*A*Wᵀ)=H A) :
    (∫⁻ D, ENNReal.ofReal (∏ i : Fin I.1.blockCount,
      Real.exp (-(1/2 : ℝ)*∑ ab : Fin (I.1.sizes i) × Fin (I.1.sizes i), (D i ab)^2)) *
        realSchurAtomicNativeCore F I k H D) =
      ∫⁻ v : Fin I.1.blockCount → ℝ × (ℝ × ℝ),
        realSchurAtomicNativeCore F I k H
          (fun i => realSchurNativeCanonicalEntries (I.1.sizes i) (v i))
        ∂Measure.pi (fun i => realSchurNativeSpectralMeasure (I.1.sizes i) 1) := by
  rw [realSchurNativeGaussianProduct_lintegral I.1.sizes 1 (by norm_num)
    (realSchurAtomicNativeCore F I k H) (realSchurAtomicNativeCore_measurable F I k H hH)
    (realSchurAtomicNativeCore_support F I k H)]
  exact realSchurNativeProduct_spectral_lintegral I.1.sizes I.1.sizes_small 1 (by norm_num)
    (realSchurAtomicNativeCore F I k H) (realSchurAtomicNativeCore_measurable F I k H hH)
    (realSchurAtomicNativeCore_separate_invariant F I k H hH hInv)

#print axioms realSchurAtomicNativeCore_single_rotation
#print axioms realSchurAtomicNativeCore_separate_invariant
#print axioms realSchurAtomicNativeCore_spectral_lintegral
end SpectralRadiusUpperTail

import SpectralRadiusUpperTail.RealSchurNativeGaussianCoordinates
import SpectralRadiusUpperTail.FiniteCoordinateCanonicalization

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix BigOperators

theorem realSchurNativeProduct_canonical_value
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, s i=1 ∨ s i=2)
    (H : ((i : Fin m) → (Fin (s i) × Fin (s i)) → ℝ) → ℝ≥0∞)
    (hInv : ∀ i D (Q : Matrix (Fin (s i)) (Fin (s i)) ℝ), Qᵀ*Q=1 →
      ∀ A : Matrix (Fin (s i)) (Fin (s i)) ℝ,
        H (Function.update D i (fun ab => (Q*A*Qᵀ) ab.1 ab.2))=
          H (Function.update D i (fun ab => A ab.1 ab.2)))
    (D : (i : Fin m) → (Fin (s i) × Fin (s i)) → ℝ) :
    H D=H (fun i => realSchurNativeCanonicalEntries (s i) (realSchurNativeSpectralCoordinates (s i) (D i))) := by
  apply finite_coordinate_canonicalization
    (fun i A => realSchurNativeCanonicalEntries (s i) (realSchurNativeSpectralCoordinates (s i) A)) H _ D
  intro A i
  have hh := realSchurNativeInvariant_canonical_value (s i) (hs i)
    (fun B => H (Function.update A i B)) (hInv i A) (A i)
  simpa only [Function.update_eq_self] using hh

/-- Exact finite-product transport for mixed native scalar and pair blocks. -/
theorem realSchurNativeProduct_spectral_lintegral
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, s i=1 ∨ s i=2)
    (n : ℝ) (hn : 0 < n)
    (H : ((i : Fin m) → (Fin (s i) × Fin (s i)) → ℝ) → ℝ≥0∞) (hH : Measurable H)
    (hInv : ∀ i D (Q : Matrix (Fin (s i)) (Fin (s i)) ℝ), Qᵀ*Q=1 →
      ∀ A : Matrix (Fin (s i)) (Fin (s i)) ℝ,
        H (Function.update D i (fun ab => (Q*A*Qᵀ) ab.1 ab.2))=
          H (Function.update D i (fun ab => A ab.1 ab.2))) :
    (∫⁻ D, H D ∂Measure.pi (fun i => realSchurNativeGaussianMeasure (s i) n)) =
      ∫⁻ v : Fin m → ℝ × (ℝ × ℝ), H (fun i => realSchurNativeCanonicalEntries (s i) (v i))
        ∂Measure.pi (fun i => realSchurNativeSpectralMeasure (s i) n) := by
  let : ∀ i, IsFiniteMeasure (realSchurNativeGaussianMeasure (s i) n) :=
    fun i => realSchurNativeGaussianMeasure_finite (s i) n hn
  let : ∀ i, IsFiniteMeasure (realSchurNativeSpectralMeasure (s i) n) :=
    fun i => realSchurNativeSpectralMeasure_finite (s i) n hn
  have hmap := Measure.pi_map_pi (μ := fun i => realSchurNativeGaussianMeasure (s i) n)
    (f := fun i => realSchurNativeSpectralCoordinates (s i))
    (fun i => (realSchurNativeSpectralCoordinates_measurable (s i)).aemeasurable)
  have hm : Measurable (fun v : Fin m → ℝ × (ℝ × ℝ) =>
      H (fun i => realSchurNativeCanonicalEntries (s i) (v i))) := by
    apply hH.comp
    exact measurable_pi_lambda _ (fun i =>
      (realSchurNativeCanonicalEntries_measurable (s i)).comp (measurable_pi_apply i))
  simp only [realSchurNativeSpectralMeasure]
  have ht : Measurable (fun D : (i : Fin m) → (Fin (s i) × Fin (s i)) → ℝ =>
      fun i => realSchurNativeSpectralCoordinates (s i) (D i)) :=
    measurable_pi_lambda _ (fun i =>
      (realSchurNativeSpectralCoordinates_measurable (s i)).comp (measurable_pi_apply i))
  rw [← hmap,lintegral_map hm ht]
  exact lintegral_congr (fun D => realSchurNativeProduct_canonical_value s hs H hInv D)

#print axioms realSchurNativeProduct_canonical_value
#print axioms realSchurNativeProduct_spectral_lintegral
end SpectralRadiusUpperTail

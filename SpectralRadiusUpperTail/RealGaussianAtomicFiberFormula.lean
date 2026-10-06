import SpectralRadiusUpperTail.RealGaussianAtomicAtlasIntegral
import SpectralRadiusUpperTail.RealSchurAtomicDiagonalWeight

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix Matrix.Norms.Operator BigOperators

/-- One normalized actual-Gaussian chart integral for an observable
invariant under the angular conjugation. The strict-upper integral is
unrestricted and has its independent Gaussian density. -/
theorem realGaussian_atomicChart_fiber_formula
    {n : ℕ} (F : RealSchurFiniteAtlas n) (I : RealSchurFiniteCode n) (k : ℕ)
    (g : ((Fin n × Fin n) → ℝ) → ℝ≥0∞)
    (H : Matrix (RealSchurMixedCoord I.1.sizes) (RealSchurMixedCoord I.1.sizes) ℝ → ℝ≥0∞)
    (hH : Measurable H)
    (hrep : ∀ t ∈ F.atomicSource I k, g (F.output I k t)=H t.2.val) :
    (∫⁻ t in F.atomicSource I k,
      ENNReal.ofReal (realSchurMixedJacobianWeight I.1.sizes 0 t) *
        (realGaussianFixedDensity n (F.output I k t) *
          ((realSchurAtomicMultiplicity n (Matrix.of (F.output I k t).curry))⁻¹ *
            g (F.output I k t))) ∂realSchurMixedCoordinateVolume I.1.sizes) =
      (ENNReal.ofReal ((Real.sqrt (2*Real.pi))^(n*n)))⁻¹ *
        ((∫⁻ w in realSchurMixedFlagAnglePatch I.1.sizes I.1.sizes_pos
          (F.marker I) (F.marker_injective I) (F.frames I) k,
            ENNReal.ofReal |realSchurMixedAngularJacobian I.1.sizes w|) *
          (∫⁻ d in realSchurAtomicDiagonalSource I.1.sizes I.2.2,
            (ENNReal.ofReal (realSchurMixedDiagonalGaussianJacobian I.1.sizes d) *
              realSchurAtomicDiagonalMultiplicityWeight F I k d) *
            (∫⁻ u : RealSchurMixedStrictUpperEntry I.1.sizes → ℝ,
              ENNReal.ofReal (Real.exp (-(∑ p, (u p)^2)/2)) *
                H (realSchurMixedUpperEntryJoin I.1.sizes d u)))) := by
  let C := (ENNReal.ofReal ((Real.sqrt (2*Real.pi))^(n*n)))⁻¹
  have hpos : 0 < (Real.sqrt (2*Real.pi))^(n*n) := by positivity
  have hC : C ≠ ∞ := ENNReal.inv_ne_top.mpr (ne_of_gt (ENNReal.ofReal_pos.mpr hpos))
  let W := realSchurAtomicDiagonalMultiplicityWeight F I k
  let V := fun t : RealSchurMixedTangent I.1.sizes =>
    ENNReal.ofReal (realSchurMixedJacobianWeight I.1.sizes 0 t) *
      (ENNReal.ofReal (realMatrixGaussianWeight (RealSchurMixedCoord I.1.sizes) t.2.val) *
        (W (realSchurMixedTangentEntries I.1.sizes t).2.1 * H t.2.val))
  calc
    _ = ∫⁻ t in F.atomicSource I k, C * V t ∂realSchurMixedCoordinateVolume I.1.sizes := by
      apply setLIntegral_congr_fun (F.measurableSet_atomicSource I k)
      intro t ht
      dsimp only
      rw [F.output_density,realSchurAtomicMultiplicity_output_eq_diagonal F I k t ht,
        hrep t ht,ENNReal.ofReal_div_of_pos hpos,div_eq_mul_inv]
      dsimp [C,V,W]
      ac_rfl
    _ = C * ∫⁻ t in F.atomicSource I k, V t ∂realSchurMixedCoordinateVolume I.1.sizes :=
      lintegral_const_mul' C V hC
    _ = _ := by
      congr 1
      exact realSchurAtomicFlagSource_weighted_gaussian I.1.sizes I.1.sizes_pos
        (F.marker I) (F.marker_injective I) (F.frames I) k I.2.2 W H
        (realSchurAtomicDiagonalMultiplicityWeight_measurable F I k) hH

/-- Complete actual Gaussian disintegration down to atomic diagonal
blocks and independent strictly-upper entries. No conditional Schur law
or unidentified normalization is assumed. -/
theorem realGaussian_lintegral_atomicFibers
    (n : ℕ) (F : RealSchurFiniteAtlas n)
    (g : ((Fin n × Fin n) → ℝ) → ℝ≥0∞) (hg : Measurable g)
    (H : ∀ I : RealSchurFiniteCode n,
      Matrix (RealSchurMixedCoord I.1.sizes) (RealSchurMixedCoord I.1.sizes) ℝ → ℝ≥0∞)
    (hH : ∀ I, Measurable (H I))
    (hrep : ∀ I k t, t ∈ F.atomicSource I k → g (F.output I k t)=H I t.2.val) :
    (∫⁻ x, g x ∂gaussianMatrixLaw n) =
      ∑ I : RealSchurFiniteCode n, ∑' k,
        (ENNReal.ofReal ((Real.sqrt (2*Real.pi))^(n*n)))⁻¹ *
          ((∫⁻ w in realSchurMixedFlagAnglePatch I.1.sizes I.1.sizes_pos
            (F.marker I) (F.marker_injective I) (F.frames I) k,
              ENNReal.ofReal |realSchurMixedAngularJacobian I.1.sizes w|) *
            (∫⁻ d in realSchurAtomicDiagonalSource I.1.sizes I.2.2,
              (ENNReal.ofReal (realSchurMixedDiagonalGaussianJacobian I.1.sizes d) *
                realSchurAtomicDiagonalMultiplicityWeight F I k d) *
              (∫⁻ u : RealSchurMixedStrictUpperEntry I.1.sizes → ℝ,
                ENNReal.ofReal (Real.exp (-(∑ p, (u p)^2)/2)) *
                  H I (realSchurMixedUpperEntryJoin I.1.sizes d u)))) := by
  classical
  rw [realGaussian_lintegral_atomicAtlas n F g hg]
  apply Finset.sum_congr rfl
  intro I _
  apply tsum_congr
  intro k
  exact realGaussian_atomicChart_fiber_formula F I k g (H I) (hH I) (hrep I k)

#print axioms realGaussian_atomicChart_fiber_formula
#print axioms realGaussian_lintegral_atomicFibers
end SpectralRadiusUpperTail

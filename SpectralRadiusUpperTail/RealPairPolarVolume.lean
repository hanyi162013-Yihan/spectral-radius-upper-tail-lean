import SpectralRadiusUpperTail.RealPairCartesianVolume
import Mathlib.Analysis.SpecialFunctions.PolarCoord

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix

private theorem lintegral_pair_reorder
    (f : ((ℝ × ℝ) × (ℝ × ℝ)) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z, f z) = ∫⁻ x : ℝ, ∫⁻ q : ℝ, ∫⁻ v : ℝ × ℝ, f ((x,v.1),(v.2,q)) := by
  change (∫⁻ z, f z ∂(volume : Measure (ℝ × ℝ)).prod volume)=_
  rw [lintegral_prod f hf.aemeasurable]
  have houter : Measurable (fun xa : ℝ × ℝ => ∫⁻ pq : ℝ × ℝ, f (xa,pq)) :=
    hf.lintegral_prod_right'
  rw [show (∫⁻ xa : ℝ × ℝ, ∫⁻ pq : ℝ × ℝ, f (xa,pq)) =
      ∫⁻ x : ℝ, ∫⁻ a : ℝ, ∫⁻ pq : ℝ × ℝ, f ((x,a),pq) from
    lintegral_prod _ houter.aemeasurable]
  apply lintegral_congr
  intro x
  have hswap : (∫⁻ a : ℝ, ∫⁻ p : ℝ, ∫⁻ q : ℝ, f ((x,a),(p,q))) =
      ∫⁻ q : ℝ, ∫⁻ a : ℝ, ∫⁻ p : ℝ, f ((x,a),(p,q)) := by
    calc
      _ = ∫⁻ a : ℝ, ∫⁻ q : ℝ, ∫⁻ p : ℝ, f ((x,a),(p,q)) := by
        apply lintegral_congr
        intro a
        exact lintegral_lintegral_swap (hf.comp (by fun_prop)).aemeasurable
      _ = _ := by
        have h : Measurable (fun z : (ℝ × ℝ) × ℝ => f ((x,z.1.1),(z.2,z.1.2))) :=
          hf.comp (by fun_prop)
        exact lintegral_lintegral_swap h.lintegral_prod_right'.aemeasurable
  calc
    _ = ∫⁻ a : ℝ, ∫⁻ p : ℝ, ∫⁻ q : ℝ, f ((x,a),(p,q)) := by
      apply lintegral_congr
      intro a
      exact lintegral_prod _ (hf.comp (by fun_prop)).aemeasurable
    _ = ∫⁻ q : ℝ, ∫⁻ a : ℝ, ∫⁻ p : ℝ, f ((x,a),(p,q)) := hswap
    _ = _ := by
      apply lintegral_congr
      intro q
      exact (lintegral_prod (fun v : ℝ × ℝ => f ((x,v.1),(v.2,q)))
        (hf.comp (by fun_prop)).aemeasurable).symm

/-- A complete entry-volume formula for real two-dimensional matrices,
using polar coordinates for the symmetric traceless part. The excluded
polar ray is null; this is a global integral identity. -/
theorem realPair_polar_lintegral
    (g : ((Fin 2 × Fin 2) → ℝ) → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ A, g A) = 4 *
      (∫⁻ x : ℝ, ∫⁻ q : ℝ, ∫⁻ r in Set.Ioi (0 : ℝ),
        ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi,
          ENNReal.ofReal r * g (fun ij =>
            realPairCartesianMatrix x (r*Real.cos θ) (r*Real.sin θ) q ij.1 ij.2)) := by
  rw [realPairCartesian_lintegral]
  congr 1
  let f := fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
    g (fun ij => realPairCartesianMatrix z.1.1 z.1.2 z.2.1 z.2.2 ij.1 ij.2)
  have hf : Measurable f := by
    apply hg.comp
    apply measurable_pi_lambda
    intro ij
    rcases ij with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;> simp only [realPairCartesianMatrix] <;> fun_prop
  change (∫⁻ z, f z)=_
  rw [lintegral_pair_reorder f hf]
  apply lintegral_congr
  intro x
  apply lintegral_congr
  intro q
  rw [← lintegral_comp_polarCoord_symm (fun v : ℝ × ℝ => f ((x,v.1),(v.2,q)))]
  change (∫⁻ v in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
    ENNReal.ofReal v.1 *
      g (fun ij => realPairCartesianMatrix x (v.1*Real.cos v.2) (v.1*Real.sin v.2) q ij.1 ij.2))=_
  rw [Measure.volume_eq_prod,← Measure.prod_restrict]
  apply lintegral_prod
  apply Measurable.aemeasurable
  apply Measurable.mul
  · exact measurable_fst.ennreal_ofReal
  · apply hg.comp
    apply measurable_pi_lambda
    intro ij
    rcases ij with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;> simp only [realPairCartesianMatrix] <;> fun_prop

#print axioms realPair_polar_lintegral
end SpectralRadiusUpperTail

import SpectralRadiusUpperTail.RealGaussianAtomicNormalization
import SpectralRadiusUpperTail.RealSchurFiniteAtlasOutput
import SpectralRadiusUpperTail.RealSchurAtomicFiberIntegral

namespace SpectralRadiusUpperTail
open scoped ENNReal Matrix Matrix.Norms.Operator

noncomputable def realSchurAtomicDiagonalMultiplicityWeight {n : ℕ}
    (F : RealSchurFiniteAtlas n) (I : RealSchurFiniteCode n) (k : ℕ)
    (d : RealSchurMixedDiagonalEntry I.1.sizes → ℝ) : ℝ≥0∞ :=
  (realSchurAtomicMultiplicity n
    (realSchurFixedFlagFiberMatrix I.1.sizes I.2.1 (F.frames I k) d (0,0)))⁻¹

theorem realSchurAtomicDiagonalMultiplicityWeight_measurable {n : ℕ}
    (F : RealSchurFiniteAtlas n) (I : RealSchurFiniteCode n) (k : ℕ) :
    Measurable (realSchurAtomicDiagonalMultiplicityWeight F I k) := by
  let s := I.1.sizes
  have hU : Continuous (fun d : RealSchurMixedDiagonalEntry s → ℝ =>
      (realSchurMixedUpperEntryEquiv s).symm (d,0)) :=
    (realSchurMixedUpperEntryEquiv s).symm.toContinuousLinearEquiv.continuous.comp
      (continuous_id.prodMk continuous_const)
  have hF : Continuous (fun d : RealSchurMixedDiagonalEntry s → ℝ =>
      realSchurMixedFiberPoint s 0 d 0) := continuous_const.prodMk hU
  have hE := (realSchurMixedExpCoordinates_contDiff s 0 1).continuous.comp hF
  have hM : Continuous (fun d : RealSchurMixedDiagonalEntry s → ℝ =>
      realSchurFixedFlagFiberMatrix s I.2.1 (F.frames I k) d (0,0)) :=
    (realSchur_reindex_continuous I.2.1.symm).comp
      ((continuous_const.mul hE).mul continuous_const)
  have hm : @Measurable (RealSchurMixedDiagonalEntry s → ℝ) (Matrix (Fin n) (Fin n) ℝ)
      inferInstance (finiteMatrixMeasurableSpace n n ℝ)
      (fun d => realSchurFixedFlagFiberMatrix s I.2.1 (F.frames I k) d (0,0)) :=
    measurable_pi_lambda _ (fun i => measurable_pi_lambda _ (fun j =>
      ((continuous_apply j).comp ((continuous_apply i).comp hM)).measurable))
  exact ((realSchurAtomicMultiplicity_measurable n).comp hm).inv

/-- The reciprocal overlap count depends only on diagonal-block entries
on a complete atomic source; it does not bias strict-upper Gaussians. -/
theorem realSchurAtomicMultiplicity_output_eq_diagonal {n : ℕ}
    (F : RealSchurFiniteAtlas n) (I : RealSchurFiniteCode n) (k : ℕ)
    (t : RealSchurMixedTangent I.1.sizes)
    (ht : t ∈ realSchurAtomicFlagSource I.1.sizes I.1.sizes_pos
      (F.marker I) (F.marker_injective I) (F.frames I) k I.2.2) :
    (realSchurAtomicMultiplicity n (Matrix.of (F.output I k t).curry))⁻¹ =
      realSchurAtomicDiagonalMultiplicityWeight F I k
        (realSchurMixedTangentEntries I.1.sizes t).2.1 := by
  let s := I.1.sizes
  let d := (realSchurMixedTangentEntries s t).2.1
  let u := (realSchurMixedTangentEntries s t).2.2
  have ht' : realSchurMixedFiberPoint s t.1 d u=t := by
    apply Prod.ext
    · rfl
    · exact (realSchurMixedUpperEntryEquiv s).symm_apply_apply t.2
  have hd := (realSchurAtomicFlagSource_mem_iff_entries s I.1.sizes_pos
    (F.marker I) (F.marker_injective I) (F.frames I) k I.2.2 t).mp ht
  have hsep : (realSchurMixedUpperEntryJoin s d 0).charpoly.Separable := hd.2.1.1
  have hcount := realSchurAtomicMultiplicity_flag_fiber s I.1.sizes_pos I.2.1
    (F.frames I k) d hsep (t.1,u) (0,0)
  have hout : Matrix.of (F.output I k t).curry =
      realSchurFixedFlagFiberMatrix s I.2.1 (F.frames I k) d (t.1,u) := by
    rw [← ht']
    exact F.output_fiber I k t.1 d u
  rw [hout,hcount]
  rfl

#print axioms realSchurAtomicDiagonalMultiplicityWeight_measurable
#print axioms realSchurAtomicMultiplicity_output_eq_diagonal
end SpectralRadiusUpperTail

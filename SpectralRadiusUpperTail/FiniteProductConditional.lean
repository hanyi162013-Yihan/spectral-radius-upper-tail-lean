import SpectralRadiusUpperTail.ProductConditionalExpectation
import Mathlib.MeasureTheory.Constructions.Pi

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped MeasureTheory
variable {Ω E : Type*} [mΩ : MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {M : ℕ}

/-- Partially observe one selected row and fully observe all other rows. -/
def enlargedRowSigma (i : Fin (M+1)) (m : MeasurableSpace Ω) :
    MeasurableSpace (Fin (M+1) → Ω) := by
  letI : MeasurableSpace Ω := mΩ
  exact MeasurableSpace.comap (MeasurableEquiv.piFinSuccAbove (fun _ => Ω) i)
    (m.prod (inferInstance : MeasurableSpace (Fin M → Ω)))

lemma enlargedRowSigma_le (i : Fin (M+1)) (m : MeasurableSpace Ω) (hm : m ≤ mΩ) :
    enlargedRowSigma (mΩ := mΩ) i m ≤ (@MeasurableSpace.pi (Fin (M+1)) (fun _ => Ω) (fun _ => mΩ)) := by
  letI : MeasurableSpace Ω := mΩ
  exact (MeasurableSpace.comap_mono (partialProductSigma_le m hm)).trans
    (MeasurableEquiv.piFinSuccAbove (fun _ => Ω) i).measurable.comap_le

lemma enlargedRowSigma_current (i : Fin (M+1)) (m : MeasurableSpace Ω) :
    MeasurableSpace.comap (fun x : Fin (M+1) → Ω => x i) m ≤ enlargedRowSigma (mΩ := mΩ) i m := by
  letI : MeasurableSpace Ω := mΩ
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (M+1) => Ω) i
  have hf : @Measurable (Ω × (Fin M → Ω)) Ω
      (m.prod (inferInstance : MeasurableSpace (Fin M → Ω))) m Prod.fst :=
    @measurable_fst Ω (Fin M → Ω) m inferInstance
  exact (hf.comp (comap_measurable e)).comap_le

lemma enlargedRowSigma_other (i j : Fin (M+1)) (hj : j ≠ i) (m : MeasurableSpace Ω) :
    MeasurableSpace.comap (fun x : Fin (M+1) → Ω => x j) mΩ ≤ enlargedRowSigma (mΩ := mΩ) i m := by
  letI : MeasurableSpace Ω := mΩ
  obtain ⟨k,rfl⟩ := Fin.exists_succAbove_eq hj
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (M+1) => Ω) i
  have hs : @Measurable (Ω × (Fin M → Ω)) (Fin M → Ω)
      (m.prod (inferInstance : MeasurableSpace (Fin M → Ω))) inferInstance Prod.snd :=
    @measurable_snd Ω (Fin M → Ω) m inferInstance
  exact ((measurable_pi_apply k).comp (hs.comp (comap_measurable e))).comap_le

/-- Exact product factorization, rather than just row marginals, transports
the row conditional expectation to the enlarged matrix history. -/
theorem condExp_pi_enlargedRow (P : Fin (M+1) → Measure Ω) [∀ i, IsProbabilityMeasure (P i)]
    (i : Fin (M+1)) (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (f : Ω → E) (hf : Integrable f (P i)) :
    (@Measure.pi (Fin (M+1)) (fun _ => Ω) _ (fun _ => mΩ) P)[
      (fun x => f (x i)) | enlargedRowSigma (mΩ := mΩ) i m] =ᵐ[
        @Measure.pi (Fin (M+1)) (fun _ => Ω) _ (fun _ => mΩ) P]
      fun x => (P i)[f | m] (x i) := by
  letI : MeasurableSpace Ω := mΩ
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (M+1) => Ω) i
  let Q := Measure.pi (fun j : Fin M => P (i.succAbove j))
  have hp := measurePreserving_piFinSuccAbove P i
  have hh := condExp_prod_fst (P i) Q m hm f hf
  have hgm : StronglyMeasurable[m.prod (inferInstance : MeasurableSpace (Fin M → Ω))]
      (fun z : Ω × (Fin M → Ω) => (P i)[f | m] z.1) :=
    stronglyMeasurable_condExp.comp_measurable (@measurable_fst Ω (Fin M → Ω) m inferInstance)
  exact condExp_pullback_eq (Measure.pi P) ((P i).prod Q) e e.measurable hp.map_eq
    (m.prod inferInstance) (partialProductSigma_le m hm) (fun z => f z.1)
    (fun z => (P i)[f | m] z.1) (hf.comp_fst Q) (integrable_condExp.comp_fst Q) hgm hh

#print axioms condExp_pi_enlargedRow
end SpectralRadiusUpperTail

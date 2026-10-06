import SpectralRadiusUpperTail.FiniteProductConditional
import SpectralRadiusUpperTail.RowMajorFiltration

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped MeasureTheory
variable {α E : Type*} [MeasurableSpace α]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {M N : ℕ}

/-- Conditional expectation of a current-row function under the full product
law, relative to the actual increasing matrix filtration, is exactly its row
conditional expectation. Completed and future rows cause no extra term. -/
theorem condExp_pi_rowMajor (P : Fin M → Measure (Fin N → α))
    [∀ i, IsProbabilityMeasure (P i)] (i : Fin M) (n : ℕ)
    (f : (Fin N → α) → E) (hf : Integrable f (P i)) :
    (Measure.pi P)[(fun x => f (x i)) | rowMajorFiltration M N (i.val*N+n)] =ᵐ[Measure.pi P]
      fun x => (P i)[f | pathFiltration N n] (x i) := by
  cases M with
  | zero => exact Fin.elim0 i
  | succ M =>
    let G := enlargedRowSigma i (pathFiltration (α := α) N n)
    let F := rowMajorFiltration (α := α) (M+1) N (i.val*N+n)
    letI : MeasurableSpace (Fin (M+1) → Fin N → α) := MeasurableSpace.pi
    have hG : G ≤ (inferInstance : MeasurableSpace (Fin (M+1) → Fin N → α)) :=
      enlargedRowSigma_le i _ ((pathFiltration N).le n)
    have hFG : F ≤ G := rowMajorFiltration_le_enlarged (M+1) N n i G
      (enlargedRowSigma_current i _) (fun j hj => enlargedRowSigma_other i j hj _)
    have hh := condExp_pi_enlargedRow P i (pathFiltration N n) ((pathFiltration N).le n) f hf
    have hg : Integrable (fun x => (P i)[f | pathFiltration N n] (x i)) (Measure.pi P) :=
      (measurePreserving_eval P i).integrable_comp_of_integrable integrable_condExp
    have hgm : StronglyMeasurable[F] (fun x => (P i)[f | pathFiltration N n] (x i)) :=
      stronglyMeasurable_condExp.comp_measurable (rowMajorFiltration_current (M+1) N n i)
    calc
      _ =ᵐ[Measure.pi P] (Measure.pi P)[(Measure.pi P)[(fun x => f (x i)) | G] | F] :=
        (condExp_condExp_of_le hFG hG).symm
      _ =ᵐ[Measure.pi P] (Measure.pi P)[(fun x => (P i)[f | pathFiltration N n] (x i)) | F] :=
        condExp_congr_ae hh
      _ =ᵐ[Measure.pi P] _ := by
        rw [condExp_of_stronglyMeasurable (hFG.trans hG) hgm hg]

theorem condExp_pi_rowMajor_zero (P : Fin M → Measure (Fin N → α))
    [∀ i, IsProbabilityMeasure (P i)] (i : Fin M) (n : ℕ)
    (f : (Fin N → α) → E) (hf : Integrable f (P i))
    (hz : (P i)[f | pathFiltration N n] =ᵐ[P i] 0) :
    (Measure.pi P)[(fun x => f (x i)) | rowMajorFiltration M N (i.val*N+n)] =ᵐ[Measure.pi P] 0 := by
  apply (condExp_pi_rowMajor P i n f hf).trans
  exact (measurePreserving_eval P i).quasiMeasurePreserving.ae hz

/-- A deterministic row conditional moment bound is valid against the full
matrix past, on the same product probability space. -/
theorem condExp_pi_rowMajor_le (P : Fin M → Measure (Fin N → α))
    [∀ i, IsProbabilityMeasure (P i)] (i : Fin M) (n : ℕ)
    (f : (Fin N → α) → ℝ) (hf : Integrable f (P i)) (C : ℝ)
    (hb : ∀ᵐ x ∂P i, (P i)[f | pathFiltration N n] x ≤ C) :
    ∀ᵐ x ∂Measure.pi P,
      (Measure.pi P)[(fun y => f (y i)) | rowMajorFiltration M N (i.val*N+n)] x ≤ C := by
  have hh := condExp_pi_rowMajor P i n f hf
  have hp := (measurePreserving_eval P i).quasiMeasurePreserving.ae hb
  filter_upwards [hh,hp] with x hx hpx
  exact hx.trans_le hpx

#print axioms condExp_pi_rowMajor
#print axioms condExp_pi_rowMajor_zero
#print axioms condExp_pi_rowMajor_le
end SpectralRadiusUpperTail

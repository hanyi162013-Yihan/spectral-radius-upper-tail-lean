import SpectralRadiusUpperTail.FinitePathFiltration

namespace SpectralRadiusUpperTail
open MeasureTheory
variable {α : Type*} [MeasurableSpace α]

lemma pathFiltration_zero (N : ℕ) : pathFiltration (α := α) N 0 = ⊥ := by
  rw [pathFiltration_of_le N 0 (Nat.zero_le N)]
  have he : pathSuffix (α := α) N 0 (Nat.zero_le N) = fun _ => Fin.elim0 := by
    funext x i
    exact Fin.elim0 i
  rw [he, MeasurableSpace.comap_const]

/-- A single matrix filtration: rows are revealed consecutively, and each row
uses the already verified suffix filtration. Natural subtraction leaves future
rows at time zero, and the row filtration caps completed rows automatically. -/
def rowMajorFiltration (M N : ℕ) :
    Filtration ℕ (inferInstance : MeasurableSpace (Fin M → Fin N → α)) where
  seq r := ⨆ i : Fin M, MeasurableSpace.comap (fun x => x i) (pathFiltration N (r-i.val*N))
  mono' := by
    intro r s hrs
    exact iSup_mono fun i => MeasurableSpace.comap_mono
      ((pathFiltration N).mono (Nat.sub_le_sub_right hrs (i.val*N)))
  le' r := by
    apply iSup_le
    intro i
    exact (MeasurableSpace.comap_mono ((pathFiltration N).le _)).trans
      (measurable_pi_apply i).comap_le

lemma rowMajorFiltration_zero (M N : ℕ) : rowMajorFiltration (α := α) M N 0 = ⊥ := by
  change (⨆ i : Fin M, MeasurableSpace.comap (fun x : Fin M → Fin N → α => x i)
    (pathFiltration (α := α) N (0-i.val*N))) = ⊥
  simp only [Nat.zero_sub, pathFiltration_zero, MeasurableSpace.comap_bot, iSup_bot]

/-- The current row is observed at exactly its within-row history time. -/
lemma rowMajorFiltration_current (M N n : ℕ) (i : Fin M) :
    @Measurable (Fin M → Fin N → α) (Fin N → α)
      (rowMajorFiltration M N (i.val*N+n)) (pathFiltration N n) (fun x => x i) := by
  apply Measurable.of_comap_le
  change MeasurableSpace.comap (fun x : Fin M → Fin N → α => x i) (pathFiltration N n) ≤
    ⨆ j : Fin M, MeasurableSpace.comap (fun x : Fin M → Fin N → α => x j)
      (pathFiltration N (i.val*N+n-j.val*N))
  have h := le_iSup (fun j : Fin M => MeasurableSpace.comap (fun x : Fin M → Fin N → α => x j)
    (pathFiltration N (i.val*N+n-j.val*N))) i
  simpa only [Nat.add_sub_cancel_left] using h

/-- The true matrix past is contained in a sigma algebra that observes the
current row partially and every other row fully. The latter is only an auxiliary
sigma algebra; it is not asserted to form an increasing filtration. -/
lemma rowMajorFiltration_le_enlarged (M N n : ℕ) (i : Fin M)
    (G : MeasurableSpace (Fin M → Fin N → α))
    (hcurrent : MeasurableSpace.comap (fun x => x i) (pathFiltration N n) ≤ G)
    (hother : ∀ j : Fin M, j ≠ i →
      MeasurableSpace.comap (fun x => x j) (inferInstance : MeasurableSpace (Fin N → α)) ≤ G) :
    rowMajorFiltration M N (i.val*N+n) ≤ G := by
  change (⨆ j : Fin M, MeasurableSpace.comap (fun x => x j)
    (pathFiltration N (i.val*N+n-j.val*N))) ≤ G
  apply iSup_le
  intro j
  by_cases hj : j=i
  · subst j
    simpa only [Nat.add_sub_cancel_left] using hcurrent
  · exact (MeasurableSpace.comap_mono ((pathFiltration N).le _)).trans (hother j hj)

#print axioms rowMajorFiltration
#print axioms rowMajorFiltration_current
#print axioms rowMajorFiltration_le_enlarged
end SpectralRadiusUpperTail

import SpectralRadiusUpperTail.DensityTransition

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {α : Type*} [MeasurableSpace α]

/-- Finite-horizon density ratios; after the horizon the transition is unchanged. -/
noncomputable def doobDensity (N : ℕ) (A : (n : ℕ) → (Fin n → α) → ℝ≥0∞)
    (n : ℕ) (s : Fin n → α) (x : α) : ℝ≥0∞ :=
  if n < N then A (n+1) (Fin.cons x s) / A n s else 1

lemma doobDensity_measurable (N : ℕ) (A : (n : ℕ) → (Fin n → α) → ℝ≥0∞)
    (hA : ∀ n, Measurable (A n)) (n : ℕ) :
    Measurable (Function.uncurry (doobDensity N A n)) := by
  change Measurable (fun z : (Fin n → α) × α => doobDensity N A n z.1 z.2)
  by_cases hn : n < N
  · have h : Measurable (fun z : (Fin n → α) × α =>
        A (n+1) (Fin.cons z.2 z.1) / A n z.1) :=
      ((hA (n+1)).comp (measurable_fin_cons n)).div ((hA n).comp measurable_fst)
    simpa only [doobDensity, if_pos hn] using h
  · simpa only [doobDensity, if_neg hn] using
      (measurable_const : Measurable (fun _ : (Fin n → α) × α => (1:ℝ≥0∞)))

lemma doobDensity_normalized (μ : Measure α) [IsProbabilityMeasure μ]
    (N : ℕ) (A : (n : ℕ) → (Fin n → α) → ℝ≥0∞)
    (hzero : ∀ n ≤ N, ∀ s, A n s ≠ 0) (htop : ∀ n ≤ N, ∀ s, A n s ≠ ∞)
    (hrec : ∀ n < N, ∀ s, (∫⁻ x, A (n+1) (Fin.cons x s) ∂μ) = A n s)
    (n : ℕ) (s : Fin n → α) : (∫⁻ x, doobDensity N A n s x ∂μ) = 1 := by
  by_cases hn : n < N
  · simpa only [doobDensity, hn, if_true] using density_ratio_normalized μ
      (fun x => A (n+1) (Fin.cons x s)) (A n s)
      (hzero n hn.le s) (htop n hn.le s) (hrec n hn s)
  · simp [doobDensity, hn]

noncomputable def doobPathLaw (μ : Measure α) [SFinite μ]
    (N : ℕ) (A : (n : ℕ) → (Fin n → α) → ℝ≥0∞)
    (hA : ∀ n, Measurable (A n)) (n : ℕ) : Measure (Fin n → α) :=
  densityPathLaw μ (doobDensity N A) (doobDensity_measurable N A hA) n

/-- The finite product of conditional density ratios telescopes to the
terminal weight divided by the initial normalizer, as an equality of measures. -/
theorem doobPathLaw_density (μ : Measure α) [IsProbabilityMeasure μ]
    (N : ℕ) (A : (n : ℕ) → (Fin n → α) → ℝ≥0∞)
    (hA : ∀ n, Measurable (A n))
    (hzero : ∀ n ≤ N, ∀ s, A n s ≠ 0) (htop : ∀ n ≤ N, ∀ s, A n s ≠ ∞)
    (hrec : ∀ n < N, ∀ s, (∫⁻ x, A (n+1) (Fin.cons x s) ∂μ) = A n s)
    (n : ℕ) (hn : n ≤ N) :
    doobPathLaw μ N A hA n = (Measure.pi (fun _ : Fin n => μ)).withDensity
      (fun s => A n s / A 0 (fun i => Fin.elim0 i)) := by
  let c := A 0 (fun i => Fin.elim0 i)
  have hnorm := doobDensity_normalized μ N A hzero htop hrec
  induction n with
  | zero =>
    have hfun : (fun s : Fin 0 → α => A 0 s / A 0 (fun i => Fin.elim0 i)) = 1 := by
      funext s
      have hs : s = (fun i => Fin.elim0 i) := Subsingleton.elim _ _
      rw [hs, div_eq_mul_inv]
      exact ENNReal.mul_inv_cancel (hzero 0 (Nat.zero_le N) _) (htop 0 (Nat.zero_le N) _)
    rw [hfun, withDensity_one]
    exact (Measure.pi_of_empty (fun _ : Fin 0 => μ) (fun i => Fin.elim0 i)).symm
  | succ n ih =>
    have hn0 : n < N := by omega
    have hgn : Measurable (fun s => A n s / c) := (hA n).div measurable_const
    have hgnext : Measurable (fun s => A (n+1) s / c) := (hA (n+1)).div measurable_const
    have hfun : (fun z : (Fin n → α) × α => (A n z.1 / c) * doobDensity N A n z.1 z.2) =
        (fun z : (Fin n → α) × α => A (n+1) (Fin.cons z.2 z.1) / c) := by
      funext z
      rw [doobDensity, if_pos hn0]
      exact density_ratio_cancel _ _ _ (hzero n hn0.le z.1) (htop n hn0.le z.1)
    change ((doobPathLaw μ N A hA n) ⊗ₘ
      (densityKernel μ (doobDensity N A n) (doobDensity_measurable N A hA n))).map
        (fun z : (Fin n → α) × α => Fin.cons z.2 z.1) =
      (Measure.pi (fun _ : Fin (n+1) => μ)).withDensity (fun s => A (n+1) s / c)
    rw [ih hn0.le]
    change (((Measure.pi (fun _ : Fin n => μ)).withDensity (fun s => A n s / c)) ⊗ₘ
      (densityKernel μ (doobDensity N A n) (doobDensity_measurable N A hA n))).map
        (fun z : (Fin n → α) × α => (Fin.cons z.2 z.1 : Fin (n+1) → α)) = _
    rw [weighted_densityKernel_compProd _ μ _ hgn _
      (doobDensity_measurable N A hA n) (hnorm n), hfun,
      map_withDensity_pullback _ _ _ (measurable_fin_cons n) hgnext, iid_cons_map]

/-- An actual probability coupling of the terminal weighted product law
and the original iid law, built by sequential common-part couplings. -/
theorem doob_coupling_exists (μ : Measure α) [IsProbabilityMeasure μ]
    (N : ℕ) (A : (n : ℕ) → (Fin n → α) → ℝ≥0∞)
    (hA : ∀ n, Measurable (A n))
    (hzero : ∀ n ≤ N, ∀ s, A n s ≠ 0) (htop : ∀ n ≤ N, ∀ s, A n s ≠ ∞)
    (hrec : ∀ n < N, ∀ s, (∫⁻ x, A (n+1) (Fin.cons x s) ∂μ) = A n s) :
    ∃ Γ : Measure (Fin N → α × α), IsProbabilityMeasure Γ ∧
      Γ.map (coordinateVector Prod.fst N) =
        (Measure.pi (fun _ : Fin N => μ)).withDensity
          (fun s => A N s / A 0 (fun i => Fin.elim0 i)) ∧
      Γ.map (comparatorVector N) = Measure.pi (fun _ : Fin N => μ) := by
  let k := doobDensity N A
  let hk := doobDensity_measurable N A hA
  have hnorm := doobDensity_normalized μ N A hzero htop hrec
  refine ⟨pairedDensityPathLaw μ k hk N, pairedDensityPathLaw_probability μ k hk hnorm N, ?_,
    pairedDensityPathLaw_comparator μ k hk hnorm N⟩
  exact (pairedDensityPathLaw_source μ k hk hnorm N).trans
    (doobPathLaw_density μ N A hA hzero htop hrec N le_rfl)

#print axioms doobPathLaw_density
#print axioms doob_coupling_exists
end SpectralRadiusUpperTail

import SpectralRadiusUpperTail.RealPairCanonicalObservable

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped Matrix ENNReal BigOperators

/-- Uniform scalar coordinates for the native one- and two-dimensional
blocks. For a scalar block the two unused coordinates are zero. -/
noncomputable def realSchurNativeSpectralCoordinates (q : ℕ)
    (A : (Fin q × Fin q) → ℝ) : ℝ × (ℝ × ℝ) :=
  if h : q=2 then realPairSpectralGapCoordinates
    (fun ij => A (Fin.cast h.symm ij.1,Fin.cast h.symm ij.2))
  else (∑ i : Fin q, A (i,i),0,0)

/-- Canonical native entries. Only dimensions one and two are used. -/
noncomputable def realSchurNativeCanonicalEntries (q : ℕ)
    (v : ℝ × (ℝ × ℝ)) : (Fin q × Fin q) → ℝ :=
  fun ij => if ij.1=ij.2 then v.1 else if ij.1.val < ij.2.val
    then (realSchurPairFromCoordinates v.2.1 v.2.2).1
    else -(realSchurPairFromCoordinates v.2.1 v.2.2).2

theorem realSchurNativeSpectralCoordinates_two (A : (Fin 2 × Fin 2) → ℝ) :
    realSchurNativeSpectralCoordinates 2 A=realPairSpectralGapCoordinates A := by
  simp [realSchurNativeSpectralCoordinates]

theorem realSchurNativeSpectralCoordinates_one (A : (Fin 1 × Fin 1) → ℝ) :
    realSchurNativeSpectralCoordinates 1 A=(A (0,0),0,0) := by
  simp [realSchurNativeSpectralCoordinates]

theorem realSchurNativeCanonicalEntries_two (v : ℝ × (ℝ × ℝ)) :
    realSchurNativeCanonicalEntries 2 v=realPairGapBlockEntries v.1 v.2 := by
  ext ⟨i,j⟩
  fin_cases i <;> fin_cases j <;>
    simp [realSchurNativeCanonicalEntries,realPairGapBlockEntries,realSchurBlock]

theorem realSchurNativeCanonicalEntries_one (v : ℝ × (ℝ × ℝ)) :
    realSchurNativeCanonicalEntries 1 v=fun _ => v.1 := by
  ext ⟨i,j⟩
  have h : i=j := Subsingleton.elim _ _
  simp [realSchurNativeCanonicalEntries,h]

theorem realSchurNativeSpectralCoordinates_measurable (q : ℕ) :
    Measurable (realSchurNativeSpectralCoordinates q) := by
  unfold realSchurNativeSpectralCoordinates
  split_ifs with h
  · exact realPairSpectralGapCoordinates_measurable.comp
      (measurable_pi_lambda _ (fun ij => measurable_pi_apply _))
  · fun_prop

theorem realSchurNativeCanonicalEntries_measurable (q : ℕ) :
    Measurable (realSchurNativeCanonicalEntries q) := by
  apply measurable_pi_lambda
  intro ij
  unfold realSchurNativeCanonicalEntries
  split_ifs
  · exact measurable_fst
  · change Measurable (fun v : ℝ × (ℝ × ℝ) => (Real.sqrt (v.2.2+4*v.2.1)+Real.sqrt v.2.2)/2)
    fun_prop
  · change Measurable (fun v : ℝ × (ℝ × ℝ) => -((Real.sqrt (v.2.2+4*v.2.1)-Real.sqrt v.2.2)/2))
    fun_prop

/-- Separate orthogonal invariance suffices for the simultaneous native
block replacement; there is no need to choose a measurable frame. -/
theorem realSchurNativeInvariant_canonical_value (q : ℕ) (hq : q=1 ∨ q=2)
    (H : ((Fin q × Fin q) → ℝ) → ℝ≥0∞)
    (hInv : ∀ Q : Matrix (Fin q) (Fin q) ℝ, Qᵀ*Q=1 →
      ∀ A : Matrix (Fin q) (Fin q) ℝ,
        H (fun ij => (Q*A*Qᵀ) ij.1 ij.2)=H (fun ij => A ij.1 ij.2))
    (A : (Fin q × Fin q) → ℝ) :
    H A=H (realSchurNativeCanonicalEntries q (realSchurNativeSpectralCoordinates q A)) := by
  rcases hq with rfl | rfl
  · rw [realSchurNativeSpectralCoordinates_one,realSchurNativeCanonicalEntries_one]
    congr 1
    ext ij
    have h : ij=(0,0) := Subsingleton.elim _ _
    rw [h]
  · rw [realSchurNativeSpectralCoordinates_two,realSchurNativeCanonicalEntries_two]
    exact realPairInvariant_canonical_value H hInv A

#print axioms realSchurNativeSpectralCoordinates_measurable
#print axioms realSchurNativeCanonicalEntries_measurable
#print axioms realSchurNativeInvariant_canonical_value
end SpectralRadiusUpperTail

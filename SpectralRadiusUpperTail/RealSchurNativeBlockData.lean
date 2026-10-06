import SpectralRadiusUpperTail.RealSchurNativeScaling
import SpectralRadiusUpperTail.RealSchurBlockData

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped Matrix

noncomputable def realSchurNativeBlockData (q : ℕ) (x u : ℝ) : RealSchurBlockData :=
  if q=2 then .pair x (Real.sqrt u) else .real x

theorem realSchurNativeBlockData_admissible (q : ℕ) (x u : ℝ) (hu : q=2 → 0 < u) :
    realSchurDataAdmissible (realSchurNativeBlockData q x u) := by
  unfold realSchurNativeBlockData
  split_ifs with hq
  · exact Real.sqrt_pos.mpr (hu hq)
  · trivial

theorem realSchurNativeBlockData_law (q : ℕ) (n x u : ℝ) :
    realSchurDataLaw n (realSchurNativeBlockData q x u)=realSchurNativeGapLaw q n u := by
  unfold realSchurNativeBlockData realSchurNativeGapLaw
  split_ifs <;> rfl

theorem realSchurNativeGapProduct_scale {m : ℕ} (s : Fin m → ℕ)
    (n c : ℝ) (hn : 0 < n) (hc : 0 < c) (x u : Fin m → ℝ)
    (hu : ∀ i, s i=2 → 0 < u i) :
    MeasurePreserving (fun g : Fin m → ℝ => fun i => g i/c)
      (Measure.pi (fun i => realSchurNativeGapLaw (s i) n (u i)))
      (Measure.pi (fun i => realSchurDataLaw (n*c)
        (realSchurNativeBlockData (s i) (x i/Real.sqrt c) (u i/c)))) := by
  let : ∀ i, IsProbabilityMeasure (realSchurNativeGapLaw (s i) n (u i)) :=
    fun i => realSchurNativeGapLaw_probability (s i) n (u i) hn (hu i)
  refine ⟨by fun_prop,?_⟩
  rw [Measure.pi_map_pi (fun _ => (show Measurable (fun g : ℝ => g/c) by fun_prop).aemeasurable)]
  congr 1
  funext i
  rw [realSchurNativeGapLaw_map_div (s i) n (u i) c hn (hu i) hc,
    realSchurNativeBlockData_law]

theorem realSchurNativeBlockData_entries (q : ℕ) (hq : q=1 ∨ q=2)
    (x u g : ℝ) (hu : q=2 → 0 ≤ u) (hg : q=2 → 0 ≤ g)
    (hsmall : q ≤ 2) (a b : Fin q) :
    realSchurDataPower (realSchurNativeBlockData q x u) 1 g
      (Fin.castLE hsmall a) (Fin.castLE hsmall b)=
        realSchurNativeCanonicalEntries q (x,u,g) (a,b) := by
  rcases hq with rfl | rfl
  · have ha : a=0 := Subsingleton.elim _ _
    have hb : b=0 := Subsingleton.elim _ _
    subst a; subst b
    simp [realSchurNativeBlockData,realSchurDataPower,realSchurNativeCanonicalEntries]
  · rw [realSchurNativeCanonicalEntries_two]
    simp only [realSchurNativeBlockData,ite_true,realSchurDataPower,schurGapPowerBlock,
      pow_one,Fin.castLE_refl]
    have he : realSchurPairFromCoordinates u g=(schurGapUpper (Real.sqrt u) g,
        schurGapLower (Real.sqrt u) g) := by
      simp only [realSchurPairFromCoordinates,schurGapUpper,schurGapLower,
        max_eq_right (hg rfl),Real.sq_sqrt (hu rfl)]
    change _=realPairGapBlockEntries x (u,g) (a,b)
    unfold realPairGapBlockEntries
    rw [he]

#print axioms realSchurNativeBlockData_admissible
#print axioms realSchurNativeGapProduct_scale
#print axioms realSchurNativeBlockData_entries
end SpectralRadiusUpperTail

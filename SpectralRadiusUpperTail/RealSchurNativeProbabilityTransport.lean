import SpectralRadiusUpperTail.RealSchurNativeUpperLaw
import SpectralRadiusUpperTail.RealSchurNativeBlockData
import SpectralRadiusUpperTail.RealSchurConditionalNativeLaw

namespace SpectralRadiusUpperTail
open MeasureTheory

noncomputable def realSchurNativeCommonLaw {m : ℕ} (s : Fin m → ℕ)
    (u : Fin m → ℝ) : Measure ((Fin m → ℝ) × (SchurEntryIndex m 2 → ℝ)) :=
  (Measure.pi (fun i => realSchurNativeGapLaw (s i) 1 (u i))).prod
    (Measure.pi (fun _ => standardNormal))

def realSchurNativeCommonSelect {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, s i ≤ 2)
    (z : (Fin m → ℝ) × (SchurEntryIndex m 2 → ℝ)) :
    (Fin m → ℝ) × (RealSchurMixedStrictUpperEntry s → ℝ) :=
  (z.1,realSchurNativeUpperSelect s hs z.2)

noncomputable def realSchurNativeCommonScale {m : ℕ} (n : ℕ)
    (z : (Fin m → ℝ) × (SchurEntryIndex m 2 → ℝ)) :
    (Fin m → ℝ) × (SchurEntryIndex m 2 → ℝ) :=
  (fun i => z.1 i/(n : ℝ),z.2)

theorem realSchurNativeCommonSelect_measurePreserving {m : ℕ}
    (s : Fin m → ℕ) (hs : ∀ i, s i ≤ 2) (u : Fin m → ℝ)
    (hu : ∀ i, s i=2 → 0 < u i) :
    MeasurePreserving (realSchurNativeCommonSelect s hs)
      (realSchurNativeCommonLaw s u) (realSchurNativeConditionalLaw s u) := by
  let : ∀ i, IsProbabilityMeasure (realSchurNativeGapLaw (s i) 1 (u i)) :=
    fun i => realSchurNativeGapLaw_probability (s i) 1 (u i) (by norm_num) (hu i)
  exact (MeasurePreserving.id _).prod (realSchurNativeUpperSelect_measurePreserving s hs)

theorem realSchurNativeCommonScale_measurePreserving {m : ℕ}
    (s : Fin m → ℕ) (n : ℕ) (hn : 0 < n) (x u : Fin m → ℝ)
    (hu : ∀ i, s i=2 → 0 < u i) :
    MeasurePreserving (realSchurNativeCommonScale (m := m) n)
      (realSchurNativeCommonLaw s u)
      (realSchurGlobalLaw n (fun i => realSchurNativeBlockData (s i)
        (x i/Real.sqrt n) (u i/(n : ℝ)))) := by
  let : ∀ i, IsProbabilityMeasure (realSchurNativeGapLaw (s i) 1 (u i)) :=
    fun i => realSchurNativeGapLaw_probability (s i) 1 (u i) (by norm_num) (hu i)
  have hg := realSchurNativeGapProduct_scale s 1 (n : ℝ) (by norm_num)
    (Nat.cast_pos.mpr hn) x u hu
  simp only [one_mul] at hg
  exact hg.prod (MeasurePreserving.id _)

#print axioms realSchurNativeCommonSelect_measurePreserving
#print axioms realSchurNativeCommonScale_measurePreserving
end SpectralRadiusUpperTail

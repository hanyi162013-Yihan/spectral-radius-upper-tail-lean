import SpectralRadiusUpperTail.RealSchurFiniteCodeLebesgue

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Operator

/-- One angular-only countable atlas for each member of the finite
shape/code cover. The atlas is chosen before matrix entries are sampled. -/
structure RealSchurFiniteAtlas (n : ℕ) where
  marker : ∀ I : RealSchurFiniteCode n, Fin I.1.blockCount → ℝ
  marker_injective : ∀ I, Function.Injective (marker I)
  frames : ∀ I : RealSchurFiniteCode n, ℕ → RealSchurMixedOrthogonalFrame I.1.sizes
  covers : ∀ (I : RealSchurFiniteCode n) (Q : RealSchurMixedOrthogonalFrame I.1.sizes), ∃ k,
    Q.val*realSchurMixedBlockScalar I.1.sizes (marker I)*Q.valᵀ ∈
      (realSchurMixedMarkerRotatedChart I.1.sizes I.1.sizes_pos (marker I)
        (marker_injective I) (frames I k).val (frames I k).property).target

noncomputable def realSchurFiniteAtlas (n : ℕ) : RealSchurFiniteAtlas n := by
  classical
  let c := fun (I : RealSchurFiniteCode n) (i : Fin I.1.blockCount) => (i.val : ℝ)
  have hc : ∀ I, Function.Injective (c I) := by
    intro I i j h
    apply Fin.ext
    change (i.val : ℝ)=(j.val : ℝ) at h
    exact_mod_cast h
  have hchoice (I : RealSchurFiniteCode n) :=
    exists_realSchurMixedFlagAtlasSequence I.1.sizes I.1.sizes_pos (c I) (hc I)
  choose R hR using hchoice
  exact ⟨c,hc,R,hR⟩

noncomputable def RealSchurFiniteAtlas.source {n : ℕ} (F : RealSchurFiniteAtlas n)
    (I : RealSchurFiniteCode n) (k : ℕ) : Set (RealSchurMixedTangent I.1.sizes) :=
  realSchurMixedFlagCodedSource I.1.sizes I.1.sizes_pos (F.marker I) (F.marker_injective I)
    (F.frames I) k I.2.2

noncomputable def RealSchurFiniteAtlas.output {n : ℕ} (F : RealSchurFiniteAtlas n)
    (I : RealSchurFiniteCode n) (k : ℕ) (t : RealSchurMixedTangent I.1.sizes) :
    (Fin n × Fin n) → ℝ :=
  (realSchurFixedToMixedLinearEquiv I.2.1).symm
    (realSchurMixedRotatedEntryCoordinates I.1.sizes 0
      (F.frames I k).val (F.frames I k).property t)

theorem RealSchurFiniteAtlas.measurableSet_source {n : ℕ} (F : RealSchurFiniteAtlas n)
    (I : RealSchurFiniteCode n) (k : ℕ) : MeasurableSet (F.source I k) :=
  measurableSet_realSchurMixedFlagCodedSource I.1.sizes I.1.sizes_pos
    (F.marker I) (F.marker_injective I) (F.frames I) k I.2.2

#print axioms realSchurFiniteAtlas
#print axioms RealSchurFiniteAtlas.measurableSet_source
end SpectralRadiusUpperTail

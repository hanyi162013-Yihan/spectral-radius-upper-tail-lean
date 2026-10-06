import SpectralRadiusUpperTail.MarkedNonrealCoordinates
import SpectralRadiusUpperTail.RealSchurMixedCodeImageMultiplicity

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix Matrix.Norms.Operator

abbrev MarkedNonrealIndex (m : ℕ) := RealSchurMixedCoord (markedNonrealBlockSizes m)
abbrev MarkedNonrealCode (m : ℕ) := Fin 2 → Fin (Fintype.card (MarkedNonrealIndex m)) → Bool

/-- Angular charts for a marked plane and an unrestricted complement. -/
structure MarkedNonrealFlagAtlas (m : ℕ) (hm : 0 < m) where
  marker : Fin 2 → ℝ
  marker_injective : Function.Injective marker
  frames : ℕ → RealSchurMixedOrthogonalFrame (markedNonrealBlockSizes m)
  coverage : ∀ Q : RealSchurMixedOrthogonalFrame (markedNonrealBlockSizes m), ∃ k,
    Q.val*realSchurMixedBlockScalar (markedNonrealBlockSizes m) marker*Q.valᵀ ∈
      (realSchurMixedMarkerRotatedChart (markedNonrealBlockSizes m)
        (markedNonrealBlockSizes_pos m hm) marker marker_injective
        (frames k).val (frames k).property).target

theorem exists_markedNonrealFlagAtlas (m : ℕ) (hm : 0 < m) :
    Nonempty (MarkedNonrealFlagAtlas m hm) := by
  let c : Fin 2 → ℝ := fun i => i.val
  have hc : Function.Injective c := by
    intro i j h
    apply Fin.ext
    change (i.val : ℝ)=(j.val : ℝ) at h
    exact_mod_cast h
  obtain ⟨R,hR⟩ := exists_realSchurMixedFlagAtlasSequence (markedNonrealBlockSizes m)
    (markedNonrealBlockSizes_pos m hm) c hc
  exact ⟨⟨c,hc,R,hR⟩⟩

noncomputable def MarkedNonrealFlagAtlas.source {m : ℕ} {hm : 0 < m}
    (F : MarkedNonrealFlagAtlas m hm) (k : ℕ) (code : MarkedNonrealCode m) :=
  realSchurMixedFlagCodedSource (markedNonrealBlockSizes m) (markedNonrealBlockSizes_pos m hm)
    F.marker F.marker_injective F.frames k code

noncomputable def MarkedNonrealFlagAtlas.angleMass {m : ℕ} {hm : 0 < m}
    (F : MarkedNonrealFlagAtlas m hm) (k : ℕ) : ℝ≥0∞ :=
  ∫⁻ w in realSchurMixedFlagAnglePatch (markedNonrealBlockSizes m) (markedNonrealBlockSizes_pos m hm)
    F.marker F.marker_injective F.frames k,
      ENNReal.ofReal |realSchurMixedAngularJacobian (markedNonrealBlockSizes m) w|

noncomputable def MarkedNonrealFlagAtlas.angularMass {m : ℕ} {hm : 0 < m}
    (F : MarkedNonrealFlagAtlas m hm) : ℝ≥0∞ := ∑' k, F.angleMass k

noncomputable def MarkedNonrealFlagAtlas.output {m : ℕ} {hm : 0 < m}
    (F : MarkedNonrealFlagAtlas m hm) (k : ℕ) :=
  realSchurMixedRotatedEntryCoordinates (markedNonrealBlockSizes m) 0
    (F.frames k).val (F.frames k).property

#print axioms exists_markedNonrealFlagAtlas
end SpectralRadiusUpperTail

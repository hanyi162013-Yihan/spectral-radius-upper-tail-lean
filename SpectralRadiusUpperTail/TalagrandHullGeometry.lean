import SpectralRadiusUpperTail.EuclideanHullSeparation
import SpectralRadiusUpperTail.ConvexSetMedianTail

namespace SpectralRadiusUpperTail
open MeasureTheory Set
variable {𝕂 Ω : Type*} [RCLike 𝕂] [MeasurableSpace Ω]

def coordinateBox (N : ℕ) (K : ℝ) : Set (EuclideanSpace 𝕂 (Fin N)) :=
  {x | ∀ i, ‖x i‖ ≤ K}

lemma coordinateBox_closed (N : ℕ) (K : ℝ) : IsClosed (coordinateBox (𝕂 := 𝕂) N K) := by
  unfold coordinateBox
  simp only [setOf_forall]
  exact isClosed_iInter (fun i => isClosed_le (PiLp.continuous_apply 2 (fun _ : Fin N => 𝕂) i).norm continuous_const)

/-- The distribution-free convex-distance estimate in the only form needed
here. Its product-measure proof remains an explicit input. -/
def TalagrandHullSeparation {N : ℕ} (μ : Measure Ω)
    (X : Ω → EuclideanSpace 𝕂 (Fin N)) (q : ℝ) : Prop :=
  ∀ S T : Set (EuclideanSpace 𝕂 (Fin N)), IsClosed S → IsClosed T →
    ∀ t : ℝ, 0 ≤ t →
      (∀ x ∈ T, ∀ v ∈ mismatchHull x S, t ≤ ‖v‖) →
      μ.real (X ⁻¹' S)*μ.real (X ⁻¹' T) ≤ Real.exp (-q*t^2)

lemma measureReal_preimage_inter_of_ae {E : Type*} (μ : Measure Ω)
    (X : Ω → E) (A S : Set E) (hS : ∀ᵐ x ∂μ, X x ∈ S) :
    μ.real (X ⁻¹' (A ∩ S)) = μ.real (X ⁻¹' A) := by
  apply measureReal_congr
  filter_upwards [hS] with x hx
  change (X x ∈ A ∧ X x ∈ S) = (X x ∈ A)
  simp only [hx, and_true]

/-- Bounded coordinates turn Talagrand convex distance into Euclidean
separation. The factor 2(K+1) also handles the zero cutoff uniformly. -/
lemma convex_set_separation_of_hull {N : ℕ} (μ : Measure Ω)
    (X : Ω → EuclideanSpace 𝕂 (Fin N)) (K q : ℝ) (hK : 0 ≤ K)
    (hsupport : ∀ᵐ x ∂μ, X x ∈ coordinateBox N K)
    (hull : TalagrandHullSeparation μ X q) :
    ConvexSetSeparation μ X (q/(2*(K+1))^2) := by
  intro A B hAc hA hBc t ht hdist
  let D := 2*(K+1)
  have hD : 0 < D := by dsimp [D]; positivity
  have hh := hull (A ∩ coordinateBox N K) (B ∩ coordinateBox N K)
    (hAc.inter (coordinateBox_closed N K)) (hBc.inter (coordinateBox_closed N K))
    (t/D) (div_nonneg ht hD.le) (by
      intro x hx v hv
      apply mismatchHull_norm_lower x (A ∩ coordinateBox N K) A hA inter_subset_left D t hD ?_ ?_ v hv
      · intro y hy i
        have hd := norm_sub_le (x i) (y i)
        have hxK := hx.2 i
        have hyK := hy.2 i
        dsimp [D]
        linarith
      · intro y hy
        simpa only [dist_comm] using hdist y hy x hx.1)
  rw [measureReal_preimage_inter_of_ae μ X A (coordinateBox N K) hsupport,
    measureReal_preimage_inter_of_ae μ X B (coordinateBox N K) hsupport] at hh
  convert! hh using 1
  congr 1
  change -(q/D^2)*t^2 = -q*(t/D)^2
  field_simp
  <;> ring

#print axioms coordinateBox_closed
#print axioms measureReal_preimage_inter_of_ae
#print axioms convex_set_separation_of_hull
end SpectralRadiusUpperTail

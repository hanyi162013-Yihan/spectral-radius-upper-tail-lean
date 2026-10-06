import SpectralRadiusUpperTail.TalagrandHullEnergy
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open WithLp Set
variable {𝕂 : Type*} [RCLike 𝕂]

/-- Retain the coordinates where the Boolean mask says agreement is
required, and erase the remaining coordinates. -/
noncomputable def agreementProjection (N : ℕ) (b : Fin N → Bool) :
    EuclideanSpace 𝕂 (Fin N) →ₗ[ℝ] EuclideanSpace 𝕂 (Fin N) where
  toFun x := toLp 2 (fun i => if b i then 0 else x i)
  map_add' x y := by
    ext i
    by_cases hi : b i <;> simp [hi]
  map_smul' a x := by
    ext i
    by_cases hi : b i <;> simp [hi]

lemma agreementProjection_continuous (N : ℕ) (b : Fin N → Bool) :
    Continuous (agreementProjection (𝕂 := 𝕂) N b) := by
  let f := fun x : EuclideanSpace 𝕂 (Fin N) =>
    (fun i : Fin N => if b i then (0 : 𝕂) else x i)
  have hf : Continuous f := by
    apply continuous_pi
    intro i
    by_cases hi : b i
    · simpa [f, hi] using (continuous_const : Continuous fun _ : EuclideanSpace 𝕂 (Fin N) => (0 : 𝕂))
    · simpa [f, hi] using
        PiLp.continuous_apply 2 (fun _ : Fin N => 𝕂) i
  exact (PiLp.continuous_toLp 2 (fun _ : Fin N => 𝕂)).comp hf

/-- A mask is admissible if some target point agrees with `x` at every
coordinate where the mask is zero. -/
def dominatingMaskAdmissible {N : ℕ}
    (x : EuclideanSpace 𝕂 (Fin N))
    (A : Set (EuclideanSpace 𝕂 (Fin N)))
    (b : Fin N → Bool) : Prop :=
  ∃ y ∈ A, ∀ i, b i = false → x i = y i

lemma dominatingMaskAdmissible_iff_projection {N : ℕ}
    (x : EuclideanSpace 𝕂 (Fin N))
    (A : Set (EuclideanSpace 𝕂 (Fin N)))
    (b : Fin N → Bool) :
    dominatingMaskAdmissible x A b ↔
      agreementProjection N b x ∈ agreementProjection N b '' A := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    refine ⟨y, hy, ?_⟩
    ext i
    by_cases hi : b i
    · simp [agreementProjection, hi]
    · have hi0 : b i = false := by cases h : b i <;> simp_all
      simpa [agreementProjection, hi0] using (hxy i hi0).symm
  · rintro ⟨y, hy, heq⟩
    refine ⟨y, hy, ?_⟩
    intro i hi
    have hh := congrArg (fun z : EuclideanSpace 𝕂 (Fin N) => z i) heq
    simpa [agreementProjection, hi] using hh.symm

/-- For compact target sets, the admissibility event of each fixed
dominating mask is closed. This is the key finite-state measurability input
for the product induction. -/
lemma dominatingMaskAdmissible_closed {N : ℕ}
    (A : Set (EuclideanSpace 𝕂 (Fin N))) (hA : IsCompact A)
    (b : Fin N → Bool) :
    IsClosed {x | dominatingMaskAdmissible x A b} := by
  have him : IsClosed (agreementProjection N b '' A) :=
    (hA.image (agreementProjection_continuous N b)).isClosed
  convert him.preimage (agreementProjection_continuous N b) using 1
  ext x
  exact dominatingMaskAdmissible_iff_projection x A b

#print axioms agreementProjection_continuous
#print axioms dominatingMaskAdmissible_iff_projection
#print axioms dominatingMaskAdmissible_closed
end SpectralRadiusUpperTail

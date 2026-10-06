import SpectralRadiusUpperTail.TalagrandFiberEnergyMeasurable
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open WithLp Set
variable {𝕂 : Type*} [RCLike 𝕂]

lemma euclideanCoordinateTail_continuous (N : ℕ) :
    Continuous (euclideanCoordinateTail (𝕂 := 𝕂) N) := by
  have hfun : Continuous (fun x : EuclideanSpace 𝕂 (Fin (N+1)) =>
      fun i : Fin N => x i.succ) := by
    apply continuous_pi
    intro i
    exact PiLp.continuous_apply 2 (fun _ : Fin (N+1) => 𝕂) i.succ
  exact (PiLp.continuous_toLp 2 (fun _ : Fin N => 𝕂)).comp hfun

lemma euclideanWithHead_continuous (N : ℕ) (s : 𝕂) :
    Continuous (fun y : EuclideanSpace 𝕂 (Fin N) =>
      euclideanWithHead N s y) := by
  have hfun : Continuous (fun y : EuclideanSpace 𝕂 (Fin N) =>
      (Fin.cons s (fun i => y i) : Fin (N+1) → 𝕂)) := by
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [Fin.cons_zero] using
        (continuous_const : Continuous fun _ : EuclideanSpace 𝕂 (Fin N) => s)
    · simpa only [Function.comp_def, Fin.cons_succ] using
        PiLp.continuous_apply 2 (fun _ : Fin N => 𝕂) j
  exact (PiLp.continuous_toLp 2 (fun _ : Fin (N+1) => 𝕂)).comp hfun

lemma euclideanWithHead_joint_continuous (N : ℕ) :
    Continuous (fun z : 𝕂 × EuclideanSpace 𝕂 (Fin N) =>
      euclideanWithHead N z.1 z.2) := by
  have hfun : Continuous (fun z : 𝕂 × EuclideanSpace 𝕂 (Fin N) =>
      (Fin.cons z.1 (fun i => z.2 i) : Fin (N+1) → 𝕂)) := by
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [Fin.cons_zero] using
        (continuous_fst : Continuous (fun z : 𝕂 × EuclideanSpace 𝕂 (Fin N) => z.1))
    · simpa only [Function.comp_def, Fin.cons_succ] using
        (PiLp.continuous_apply 2 (fun _ : Fin N => 𝕂) j).comp
          (continuous_snd : Continuous (fun z : 𝕂 × EuclideanSpace 𝕂 (Fin N) => z.2))
  exact (PiLp.continuous_toLp 2 (fun _ : Fin (N+1) => 𝕂)).comp hfun

lemma matchingHeadFiber_eq_tail_image (N : ℕ)
    (x : EuclideanSpace 𝕂 (Fin (N+1)))
    (A : Set (EuclideanSpace 𝕂 (Fin (N+1)))) :
    matchingHeadFiber N x A =
      euclideanCoordinateTail N '' (A ∩ {y | y 0 = x 0}) := by
  ext z
  constructor
  · intro hz
    refine ⟨euclideanWithHead N (x 0) z, ⟨hz, by simp [euclideanWithHead]⟩, ?_⟩
    ext i
    rfl
  · rintro ⟨y, ⟨hy, hhead⟩, rfl⟩
    change euclideanWithHead N (x 0) (euclideanCoordinateTail N y) ∈ A
    have he : euclideanWithHead N (x 0) (euclideanCoordinateTail N y) = y := by
      ext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa [euclideanWithHead] using hhead.symm
      · simp [euclideanWithHead, euclideanCoordinateTail]
    rwa [he]

lemma matchingHeadFiber_compact (N : ℕ)
    (x : EuclideanSpace 𝕂 (Fin (N+1)))
    (A : Set (EuclideanSpace 𝕂 (Fin (N+1)))) (hA : IsCompact A) :
    IsCompact (matchingHeadFiber N x A) := by
  rw [matchingHeadFiber_eq_tail_image]
  have hhead : IsClosed {y : EuclideanSpace 𝕂 (Fin (N+1)) | y 0 = x 0} :=
    isClosed_eq (PiLp.continuous_apply 2 (fun _ : Fin (N+1) => 𝕂) 0) continuous_const
  exact (hA.inter_right hhead).image (euclideanCoordinateTail_continuous N)

lemma projectedTarget_compact (N : ℕ)
    (A : Set (EuclideanSpace 𝕂 (Fin (N+1)))) (hA : IsCompact A) :
    IsCompact (euclideanCoordinateTail N '' A) :=
  hA.image (euclideanCoordinateTail_continuous N)

#print axioms matchingHeadFiber_eq_tail_image
#print axioms matchingHeadFiber_compact
#print axioms projectedTarget_compact
end SpectralRadiusUpperTail

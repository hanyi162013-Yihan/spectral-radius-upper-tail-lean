import SpectralRadiusUpperTail.BoundedArrayObservableRange
import Mathlib.Analysis.Convex.Hull

namespace SpectralRadiusUpperTail
open WithLp Set
open scoped BigOperators
variable {𝕂 : Type*} [RCLike 𝕂]

lemma norm_sub_real_combination_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x y z : E) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    ‖x-(a • y+b • z)‖ ≤ a*‖x-y‖+b*‖x-z‖ := by
  have he : x-(a • y+b • z) = a • (x-y)+b • (x-z) := by
    rw [smul_sub, smul_sub]
    have hx : a • x+b • x=x := by rw [← add_smul, hab, one_smul]
    calc
      _ = (a • x+b • x)-(a • y+b • z) := by rw [hx]
      _ = _ := by abel
  rw [he]
  apply (norm_add_le _ _).trans
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg ha, abs_of_nonneg hb]

noncomputable def coordinateMismatch {N : ℕ} (x y : EuclideanSpace 𝕂 (Fin N)) :
    EuclideanSpace ℝ (Fin N) := toLp 2 (fun i => if x i=y i then 0 else 1)

noncomputable def mismatchHull {N : ℕ} (x : EuclideanSpace 𝕂 (Fin N))
    (S : Set (EuclideanSpace 𝕂 (Fin N))) : Set (EuclideanSpace ℝ (Fin N)) :=
  convexHull ℝ (coordinateMismatch x '' S)

/-- Convex combinations of coordinate mismatch vectors retain a witness in
the original convex set, with a coordinatewise displacement bound. -/
lemma mismatchHull_witness {N : ℕ} (x : EuclideanSpace 𝕂 (Fin N))
    (S A : Set (EuclideanSpace 𝕂 (Fin N))) (hA : Convex ℝ A) (hSA : S ⊆ A)
    (D : ℝ) (hD : 0 ≤ D) (hdiam : ∀ y ∈ S, ∀ i, ‖x i-y i‖ ≤ D)
    (v : EuclideanSpace ℝ (Fin N)) (hv : v ∈ mismatchHull x S) :
    ∃ y ∈ A, ∀ i, ‖x i-y i‖ ≤ D*v i := by
  let C : Set (EuclideanSpace ℝ (Fin N)) :=
    {v | ∃ y ∈ A, ∀ i, ‖x i-y i‖ ≤ D*v i}
  have hC : Convex ℝ C := by
    intro v hv w hw a b ha hb hab
    obtain ⟨y, hy, hyv⟩ := hv
    obtain ⟨z, hz, hzw⟩ := hw
    refine ⟨a • y+b • z, hA hy hz ha hb hab, ?_⟩
    intro i
    change ‖x i-(a • y i+b • z i)‖ ≤ D*(a*v i+b*w i)
    have hh := norm_sub_real_combination_le (x i) (y i) (z i) a b ha hb hab
    have h1 := mul_le_mul_of_nonneg_left (hyv i) ha
    have h2 := mul_le_mul_of_nonneg_left (hzw i) hb
    nlinarith only [hh, h1, h2]
  have hsub : coordinateMismatch x '' S ⊆ C := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨y, hSA hy, ?_⟩
    intro i
    change ‖x i-y i‖ ≤ D*(if x i=y i then 0 else 1)
    by_cases hi : x i=y i
    · simp [hi]
    · simpa [hi] using hdiam y hy i
  exact convexHull_min hsub hC hv

#print axioms norm_sub_real_combination_le
#print axioms mismatchHull_witness
end SpectralRadiusUpperTail

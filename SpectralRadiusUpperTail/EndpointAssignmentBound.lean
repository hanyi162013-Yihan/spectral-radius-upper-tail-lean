import SpectralRadiusUpperTail.FiniteAssignmentSum
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Tactic.Linarith

namespace SpectralRadiusUpperTail
open scoped BigOperators
variable {σ ι 𝕂 : Type*} [Fintype σ] [DecidableEq σ] [Fintype ι] [RCLike 𝕂]

lemma vector_norm_le_one_of_energy (p : ι → 𝕂) (hp : (∑ i, ‖p i‖^2) ≤ 1) (i : ι) :
    ‖p i‖ ≤ 1 := by
  have h : ‖p i‖^2 ≤ ∑ j, ‖p j‖^2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg ‖p j‖) (Finset.mem_univ i)
  nlinarith [norm_nonneg (p i)]

/-- Four paired-walk endpoint weights admit a one-coordinate square bound. -/
lemma endpoint_weights_le_average (p q : ι → 𝕂)
    (hq : (∑ i, ‖q i‖^2) ≤ 1) (a b c d : ι) :
    ‖p a‖ * ‖q b‖ * ‖p c‖ * ‖q d‖ ≤ (‖p a‖^2+‖p c‖^2)/2 := by
  have hb := vector_norm_le_one_of_energy q hq b
  have hd := vector_norm_le_one_of_energy q hq d
  have hbd : ‖q b‖ * ‖q d‖ ≤ 1 := by
    nlinarith [norm_nonneg (q b), norm_nonneg (q d),
      mul_nonneg (sub_nonneg.mpr hb) (norm_nonneg (q d))]
  have h := mul_le_mul_of_nonneg_left hbd (mul_nonneg (norm_nonneg (p a)) (norm_nonneg (p c)))
  nlinarith [sq_nonneg (‖p a‖-‖p c‖)]

/-- Uniform bound for every endpoint equality pattern, before imposing
injectivity of vertex labels. It saves at least one free label. -/
lemma endpoint_assignment_sum_le (p q : ι → 𝕂)
    (hp : (∑ i, ‖p i‖^2) ≤ 1) (hq : (∑ i, ‖q i‖^2) ≤ 1)
    (a b c d : σ) :
    (∑ x : σ → ι, ‖p (x a)‖*‖q (x b)‖*‖p (x c)‖*‖q (x d)‖) ≤
      (Fintype.card ι : ℝ)^(Fintype.card σ-1) := by
  calc
    _ ≤ ∑ x : σ → ι, (‖p (x a)‖^2+‖p (x c)‖^2)/2 :=
      Finset.sum_le_sum (fun x _ => endpoint_weights_le_average p q hq _ _ _ _)
    _ = (Fintype.card ι : ℝ)^(Fintype.card σ-1) * ∑ i, ‖p i‖^2 := by
      simp_rw [div_eq_mul_inv]
      rw [← Finset.sum_mul, Finset.sum_add_distrib,
        assignment_sum_one_coordinate a (fun i => ‖p i‖^2),
        assignment_sum_one_coordinate c (fun i => ‖p i‖^2)]
      ring
    _ ≤ _ := by
      simpa using mul_le_mul_of_nonneg_left hp
        (pow_nonneg (Nat.cast_nonneg (Fintype.card ι)) (Fintype.card σ-1))

/-- Coincident simple paths have two distinct endpoints and save two labels. -/
lemma endpoint_assignment_simple_path_le (p q : ι → 𝕂)
    (hp : (∑ i, ‖p i‖^2) ≤ 1) (hq : (∑ i, ‖q i‖^2) ≤ 1)
    (a b : σ) (hba : b ≠ a) :
    (∑ x : σ → ι, ‖p (x a)‖*‖q (x b)‖*‖p (x a)‖*‖q (x b)‖) ≤
      (Fintype.card ι : ℝ)^(Fintype.card σ-2) := by
  have he : (∑ x : σ → ι, ‖p (x a)‖*‖q (x b)‖*‖p (x a)‖*‖q (x b)‖) =
      ∑ x : σ → ι, ‖p (x a)‖^2*‖q (x b)‖^2 := by
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [he, assignment_sum_two_coordinates a b hba (fun i => ‖p i‖^2) (fun i => ‖q i‖^2)]
  have hprod : (∑ i, ‖p i‖^2)*(∑ i, ‖q i‖^2) ≤ 1 := by
    have hq0 : 0 ≤ ∑ i, ‖q i‖^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    nlinarith [mul_nonneg (sub_nonneg.mpr hp) hq0]
  have h := mul_le_mul_of_nonneg_left hprod
    (pow_nonneg (Nat.cast_nonneg (Fintype.card ι)) (Fintype.card σ-2))
  simpa only [mul_assoc, mul_one] using h

#print axioms vector_norm_le_one_of_energy
#print axioms endpoint_weights_le_average
#print axioms endpoint_assignment_sum_le
#print axioms endpoint_assignment_simple_path_le
end SpectralRadiusUpperTail

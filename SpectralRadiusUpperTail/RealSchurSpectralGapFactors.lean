import SpectralRadiusUpperTail.RealSchurSylvesterNondegenerate
import SpectralRadiusUpperTail.RealSchurBlockData
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped BigOperators Matrix

/-- The positive local spectral-gap factor for any two real Schur diagonal
blocks. It is a prospective factor in the mixed-block Schur Jacobian;
this definition alone does not assert a global change of variables. -/
noncomputable def realSchurSpectralGap :
    RealSchurBlockData → RealSchurBlockData → ℝ
  | .real a, .real u => |a-u|
  | .real a, .pair x y => (a-x)^2+y^2
  | .pair x y, .real a => (a-x)^2+y^2
  | .pair x y, .pair u v =>
      ((x-u)^2+(y-v)^2)*((x-u)^2+(y+v)^2)

/-- Repeated real roots or repeated upper-half-plane representatives are
the only collisions between two admissible real Schur blocks. -/
def realSchurDataSeparated : RealSchurBlockData → RealSchurBlockData → Prop
  | .real a, .real u => a ≠ u
  | .pair x y, .pair u v => x ≠ u ∨ y ≠ v
  | _, _ => True

theorem realSchurSpectralGap_symm (A B : RealSchurBlockData) :
    realSchurSpectralGap A B = realSchurSpectralGap B A := by
  cases A <;> cases B <;>
    simp [realSchurSpectralGap, abs_sub_comm] <;>
    ring

theorem realSchurSpectralGap_pos (A B : RealSchurBlockData)
    (hA : realSchurDataAdmissible A)
    (hB : realSchurDataAdmissible B)
    (hsep : realSchurDataSeparated A B) :
    0 < realSchurSpectralGap A B := by
  cases A with
  | real a =>
    cases B with
    | real u =>
      change 0 < |a-u|
      exact abs_pos.mpr (sub_ne_zero.mpr hsep)
    | pair x y =>
      change 0 < (a-x)^2+y^2
      change 0 < y at hB
      nlinarith [sq_nonneg (a-x), sq_pos_of_pos hB]
  | pair x y =>
    change 0 < y at hA
    cases B with
    | real a =>
      change 0 < (a-x)^2+y^2
      nlinarith [sq_nonneg (a-x), sq_pos_of_pos hA]
    | pair u v =>
      change 0 < v at hB
      change x ≠ u ∨ y ≠ v at hsep
      change 0 < ((x-u)^2+(y-v)^2)*((x-u)^2+(y+v)^2)
      apply mul_pos
      · rcases hsep with hx | hy
        · nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr hx),
            sq_nonneg (y-v)]
        · nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr hy),
            sq_nonneg (x-u)]
      · nlinarith [sq_nonneg (x-u), sq_pos_of_pos (add_pos hA hB)]

theorem realSchurSpectralGap_scalar_pair
    (a x b c y : ℝ) (hbc : b*c = y^2) :
    realSchurSpectralGap (.real a) (.pair x y) =
      Matrix.det (realSchurBlock x b c - Matrix.scalar (Fin 2) a) := by
  rw [realSchur_scalar_pair_factor a x b c y hbc]
  change (a-x)^2+y^2 = ‖((x-a : ℝ) : ℂ)+y*Complex.I‖^2
  rw [← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im]
  ring

theorem realSchurSpectralGap_pair_pair
    (x b c u d e y v : ℝ)
    (hbc : b*c = y^2) (hde : d*e = v^2) :
    realSchurSpectralGap (.pair x y) (.pair u v) =
      Matrix.det (realSchurPairPairSylvester x b c u d e) := by
  rw [realSchur_pair_pair_factor x b c u d e y v hbc hde]
  rfl

/-- Product of the local mixed-block gap factors over an ordered finite
family. This is algebraic bookkeeping, not the Jacobian of a global atlas. -/
noncomputable def realSchurLocalGapProduct {m : ℕ}
    (B : Fin m → RealSchurBlockData) : ℝ :=
  ∏ p ∈ Finset.univ.filter (fun p : Fin m × Fin m => p.1 < p.2),
    realSchurSpectralGap (B p.1) (B p.2)

theorem realSchurLocalGapProduct_pos {m : ℕ}
    (B : Fin m → RealSchurBlockData)
    (hadm : ∀ i, realSchurDataAdmissible (B i))
    (hsep : ∀ i j, i < j → realSchurDataSeparated (B i) (B j)) :
    0 < realSchurLocalGapProduct B := by
  unfold realSchurLocalGapProduct
  apply Finset.prod_pos
  intro p hp
  have hij : p.1 < p.2 := (Finset.mem_filter.mp hp).2
  exact realSchurSpectralGap_pos (B p.1) (B p.2)
    (hadm p.1) (hadm p.2) (hsep p.1 p.2 hij)

#print axioms realSchurSpectralGap_symm
#print axioms realSchurSpectralGap_pos
#print axioms realSchurSpectralGap_scalar_pair
#print axioms realSchurSpectralGap_pair_pair
#print axioms realSchurLocalGapProduct_pos
end SpectralRadiusUpperTail

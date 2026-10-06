import SpectralRadiusUpperTail.MarkedRealStereoInverse
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix BigOperators

theorem markedRealVectorCons_reconstruct (m : ℕ)
    (v : RealSchurMixedCoord (markedRealTwoBlockSizes m) → ℝ) :
    markedRealVectorCons m (v (markedRealFirstCoordinate m)) (fun i => v ⟨1,i⟩) = v := by
  apply markedRealVectorCons_ext m
  · exact markedRealVectorCons_first m _ _
  · intro i
    exact markedRealVectorCons_complement m _ _ i

theorem markedRealVector_energy_split (m : ℕ)
    (v : RealSchurMixedCoord (markedRealTwoBlockSizes m) → ℝ) :
    (∑ i, (v i)^2) = (v (markedRealFirstCoordinate m))^2 +
      ∑ i : Fin m, (v ⟨1,i⟩)^2 := by
  have h := markedRealVectorCons_sum m (v (markedRealFirstCoordinate m))
    (fun i => v ⟨1,i⟩) (fun t => t^2)
  rwa [markedRealVectorCons_reconstruct] at h

/-- Every unit column in the open positive hemisphere occurs in the
explicit chart, with parameter squared length below one. -/
theorem markedRealStereoFrame_covers_positive_unit_column (m : ℕ)
    (v : RealSchurMixedCoord (markedRealTwoBlockSizes m) → ℝ)
    (hunit : (∑ i, (v i)^2) = 1)
    (hpos : 0 < v (markedRealFirstCoordinate m)) :
    ∃ u : Fin m → ℝ, u ⬝ᵥ u < 1 ∧
      ∀ i, markedRealStereoFrame m u i (markedRealFirstCoordinate m) = v i := by
  let a := v (markedRealFirstCoordinate m)
  have ha : 0 < a := hpos
  have hne : 1+a ≠ 0 := by positivity
  have henergy : a^2 + ∑ i : Fin m, (v ⟨1,i⟩)^2 = 1 := by
    rw [← markedRealVector_energy_split]
    exact hunit
  let u : Fin m → ℝ := fun i => v ⟨1,i⟩/(1+a)
  have hdot : u ⬝ᵥ u = (∑ i : Fin m, (v ⟨1,i⟩)^2)/(1+a)^2 := by
    simp only [u, dotProduct, ← pow_two, div_pow, Finset.sum_div]
  have hu : u ⬝ᵥ u < 1 := by
    rw [hdot]
    apply (div_lt_one (sq_pos_of_pos (by positivity : 0 < 1+a))).mpr
    nlinarith
  have hd : markedRealStereoDenom m u = 2/(1+a) := by
    unfold markedRealStereoDenom
    rw [hdot]
    field_simp [hne]
    nlinarith
  have hfirst : markedRealStereoFrame m u (markedRealFirstCoordinate m)
      (markedRealFirstCoordinate m) = a := by
    have h := markedRealStereoFrame_one_add_first m u
    rw [hd] at h
    have he : 2/(2/(1+a)) = 1+a := by field_simp
    rw [he] at h
    linarith
  have hcomp (i : Fin m) : markedRealStereoFrame m u ⟨1,i⟩
      (markedRealFirstCoordinate m) = v ⟨1,i⟩ := by
    rw [markedRealStereoFrame_complement_first, hd]
    dsimp [u]
    field_simp [hne]
    <;> ring
  refine ⟨u, hu, ?_⟩
  have heq := markedRealVectorCons_ext m
    (fun i => markedRealStereoFrame m u i (markedRealFirstCoordinate m)) v hfirst hcomp
  intro i
  exact congrFun heq i

#print axioms markedRealVectorCons_reconstruct
#print axioms markedRealVector_energy_split
#print axioms markedRealStereoFrame_covers_positive_unit_column
end SpectralRadiusUpperTail

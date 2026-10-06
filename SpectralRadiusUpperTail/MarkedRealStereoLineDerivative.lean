import SpectralRadiusUpperTail.MarkedRealStereoInverse
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix BigOperators

theorem markedRealStereoDenom_line_hasDerivAt
    (m : ℕ) (u h : Fin m → ℝ) :
    HasDerivAt (fun t : ℝ => markedRealStereoDenom m (u+t • h))
      (2*(u ⬝ᵥ h)) 0 := by
  have hcoord (i : Fin m) : HasDerivAt (fun t : ℝ => u i+t*h i) (h i) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (h i)).const_add (u i)
  have hsq (i : Fin m) : HasDerivAt (fun t : ℝ => (u i+t*h i)^2) (2*u i*h i) 0 := by
    convert! (hcoord i).pow 2 using 1 <;> simp
  have ht := (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hsq i)).const_add 1
  convert! ht using 1
  · funext t
    simp only [markedRealStereoDenom, dotProduct, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, pow_two]
  · simp only [dotProduct, Finset.mul_sum, mul_assoc]

theorem markedRealStereoFrame_first_line_hasDerivAt
    (m : ℕ) (u h : Fin m → ℝ) :
    HasDerivAt (fun t : ℝ => markedRealStereoFrame m (u+t • h)
      (markedRealFirstCoordinate m) (markedRealFirstCoordinate m))
      (-4*(u ⬝ᵥ h)/(markedRealStereoDenom m u)^2) 0 := by
  have hd := markedRealStereoDenom_line_hasDerivAt m u h
  have hn : markedRealStereoDenom m (u+(0 : ℝ) • h) ≠ 0 :=
    (markedRealStereoDenom_pos m _).ne'
  have ht := ((hasDerivAt_const (0 : ℝ) (2 : ℝ)).div hd hn).sub_const 1
  have he (t : ℝ) : markedRealStereoFrame m (u+t • h)
      (markedRealFirstCoordinate m) (markedRealFirstCoordinate m) =
      2/markedRealStereoDenom m (u+t • h)-1 := by
    have hh := markedRealStereoFrame_one_add_first m (u+t • h)
    linarith
  simp only [he]
  convert! ht using 1
  simp only [zero_smul, add_zero, zero_mul, zero_sub]
  ring

theorem markedRealStereoFrame_complement_line_hasDerivAt
    (m : ℕ) (u h : Fin m → ℝ) (i : Fin m) :
    HasDerivAt (fun t : ℝ => markedRealStereoFrame m (u+t • h)
      ⟨1,i⟩ (markedRealFirstCoordinate m))
      (2*h i/markedRealStereoDenom m u -
        4*u i*(u ⬝ᵥ h)/(markedRealStereoDenom m u)^2) 0 := by
  have hd := markedRealStereoDenom_line_hasDerivAt m u h
  have hn : markedRealStereoDenom m (u+(0 : ℝ) • h) ≠ 0 :=
    (markedRealStereoDenom_pos m _).ne'
  have hcoord : HasDerivAt (fun t : ℝ => 2*(u i+t*h i)) (2*h i) 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).mul_const (h i)).const_add (u i)).const_mul 2
  have ht := hcoord.div hd hn
  simp only [markedRealStereoFrame_complement_first, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  convert! ht using 1
  simp only [zero_smul, add_zero, zero_mul]
  field_simp [(markedRealStereoDenom_pos m u).ne']
  <;> ring

#print axioms markedRealStereoDenom_line_hasDerivAt
#print axioms markedRealStereoFrame_first_line_hasDerivAt
#print axioms markedRealStereoFrame_complement_line_hasDerivAt
end SpectralRadiusUpperTail

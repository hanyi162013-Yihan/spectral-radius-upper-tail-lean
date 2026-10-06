import SpectralRadiusUpperTail.RealSchurDiagonalCharpoly
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

private lemma complex_pair_quadratic_factor (x y : ℝ) :
    (Polynomial.X : Polynomial ℂ)^2 - Polynomial.C (2*(x : ℂ))*Polynomial.X +
      Polynomial.C ((x : ℂ)^2+(y : ℂ)^2) =
      (Polynomial.X-Polynomial.C ((x : ℂ)+(y : ℂ)*Complex.I)) *
      (Polynomial.X-Polynomial.C ((x : ℂ)-(y : ℂ)*Complex.I)) := by
  let u : ℂ := (x : ℂ)+(y : ℂ)*Complex.I
  let v : ℂ := (x : ℂ)-(y : ℂ)*Complex.I
  have hs : u+v = 2*(x : ℂ) := by dsimp [u,v]; ring
  have hp : u*v = (x : ℂ)^2+(y : ℂ)^2 := by
    calc
      u*v = (x : ℂ)^2-(y : ℂ)^2*Complex.I^2 := by dsimp [u,v]; ring
      _ = _ := by rw [Complex.I_sq]; ring
  calc
    _ = Polynomial.X^2-Polynomial.C (u+v)*Polynomial.X+
      Polynomial.C (u*v) := by rw [hs,hp]
    _ = (Polynomial.X-Polynomial.C u)*(Polynomial.X-Polynomial.C v) := by
      simp only [map_add, map_mul]
      ring
    _ = _ := rfl

private lemma realSchurDataPower_complex_charpoly (B : RealSchurBlockData) (s : ℝ) :
    ((realSchurDataPower B 1 s).map Complex.ofRealHom).charpoly =
      match B with
      | .real x => Polynomial.X * (Polynomial.X-Polynomial.C (x : ℂ))
      | .pair x y =>
          (Polynomial.X-Polynomial.C ((x : ℂ)+(y : ℂ)*Complex.I)) *
          (Polynomial.X-Polynomial.C ((x : ℂ)-(y : ℂ)*Complex.I)) := by
  cases B with
  | real x =>
    rw [Matrix.charpoly_map, realSchurDataPower_charpoly]
    simp
  | pair x y =>
    rw [Matrix.charpoly_map, realSchurDataPower_charpoly]
    simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul,
      Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
    norm_num
    simpa only [map_add, map_sub, map_mul, map_pow] using
      (complex_pair_quadratic_factor x y)

/-- A padded real block has exactly its prescribed real or conjugate-pair
eigenvalues, plus an artificial zero for a 1×1 block. -/
theorem realSchurDataPower_spectrum_norm_le (B : RealSchurBlockData)
    (s : ℝ) (z : ℂ)
    (hz : z ∈ spectrum ℂ ((realSchurDataPower B 1 s).map Complex.ofRealHom)) :
    ‖z‖ ≤ realSchurDataRadius B := by
  have hroot := (Matrix.mem_spectrum_iff_isRoot_charpoly).mp hz
  rw [realSchurDataPower_complex_charpoly B s] at hroot
  cases B with
  | real x =>
    have hz0 : z*(z-(x : ℂ)) = 0 := by simpa [Polynomial.IsRoot] using hroot
    rcases mul_eq_zero.mp hz0 with hzero | hx
    · subst z
      simp [realSchurDataRadius]
    · have hzval : z = (x : ℂ) := sub_eq_zero.mp hx
      rw [hzval]
      simp [realSchurDataRadius]
  | pair x y =>
    let u : ℂ := (x : ℂ)+(y : ℂ)*Complex.I
    let v : ℂ := (x : ℂ)-(y : ℂ)*Complex.I
    have hz0 : (z-u)*(z-v) = 0 := by
      simpa [Polynomial.IsRoot, u, v] using hroot
    rcases mul_eq_zero.mp hz0 with hu | hv
    · rw [sub_eq_zero.mp hu]
      rfl
    · rw [sub_eq_zero.mp hv]
      have hconj : v = star u := by dsimp [u,v]; simp; ring
      rw [hconj, norm_star]
      rfl

/-- The prescribed block radius is attained by an eigenvalue; for a real
block the padded zero is ignored. -/
theorem realSchurDataPower_radius_witness (B : RealSchurBlockData)
    (s : ℝ) :
    ∃ z : ℂ, z ∈ spectrum ℂ
      ((realSchurDataPower B 1 s).map Complex.ofRealHom) ∧
      ‖z‖ = realSchurDataRadius B := by
  cases B with
  | real x =>
    refine ⟨(x : ℂ), ?_, by simp [realSchurDataRadius]⟩
    apply (Matrix.mem_spectrum_iff_isRoot_charpoly).mpr
    rw [realSchurDataPower_complex_charpoly]
    simp [Polynomial.IsRoot]
  | pair x y =>
    refine ⟨(x : ℂ)+(y : ℂ)*Complex.I, ?_, rfl⟩
    apply (Matrix.mem_spectrum_iff_isRoot_charpoly).mpr
    rw [realSchurDataPower_complex_charpoly]
    simp [Polynomial.IsRoot]

#print axioms realSchurDataPower_spectrum_norm_le
#print axioms realSchurDataPower_radius_witness
end SpectralRadiusUpperTail

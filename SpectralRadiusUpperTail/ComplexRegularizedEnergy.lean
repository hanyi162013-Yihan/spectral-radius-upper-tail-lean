import SpectralRadiusUpperTail.ComplexRegularizedLogDetGap
import SpectralRadiusUpperTail.NormalizedFrobeniusEnergy

namespace SpectralRadiusUpperTail
open scoped BigOperators Matrix.Norms.Frobenius ComplexOrder MatrixOrder

lemma complex_frobenius_scalar_one_sq (n : ℕ) (z : ℂ) :
    ‖z • (1 : Matrix (Fin n) (Fin n) ℂ)‖^2 = (n : ℝ)*‖z‖^2 := by
  rw [norm_smul, mul_pow, matrix_frobenius_sq_sum]
  simp [Matrix.one_apply, apply_ite, mul_comm]

lemma complexRegularizedLogDet_upper_energy {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (z : ℂ) (s : ℝ) (hs : 0 < s) :
    complexRegularizedLogDet A z s ≤ ‖A-z • 1‖^2+(n : ℝ)*s := by
  have hh := posSemidef_shift_logDet_upper _
    (Matrix.posSemidef_conjTranspose_mul_self (A-z • 1)) s hs
  rw [Matrix.trace_mul_comm, ← frobenius_norm_sq_trace] at hh
  convert! hh using 1

lemma normalized_complexRegularizedLogDet_floor {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) (s : ℝ) (hs : 0 < s) :
    Real.log s ≤ complexRegularizedLogDet A z s/(n : ℝ) := by
  have hH := Matrix.posSemidef_conjTranspose_mul_self (A-z • 1)
  have hh := (posSemidef_shift_det_lower _ hH s hs.le).1
  have hl := Real.log_le_log (pow_pos hs n) hh
  have he : (n : ℝ)*Real.log s ≤ complexRegularizedLogDet A z s := by
    convert! hl using 1
    simp only [Real.log_pow]
  exact (le_div_iff₀ (Nat.cast_pos.mpr hn)).mpr (by simpa only [mul_comm] using he)

lemma normalized_complexRegularizedLogDet_energy_bound {n : ℕ} (hn : 0 < n)
    (x : Fin n × Fin n → ℂ) (z : ℂ) (s R : ℝ) (hs : 0 < s) (hz : ‖z‖ ≤ R) :
    complexRegularizedLogDet (normalizedIidMatrix x) z s/(n : ℝ) ≤
      2*averageEntryEnergy x+2*R^2+s := by
  let A := normalizedIidMatrix x
  let B := z • (1 : Matrix (Fin n) (Fin n) ℂ)
  have hh : ‖A-B‖^2 ≤ 2*‖A‖^2+2*‖B‖^2 := by
    have ht := norm_sub_le A B
    have hs := sq_nonneg (‖A‖-‖B‖)
    nlinarith [norm_nonneg (A-B), norm_nonneg A, norm_nonneg B]
  have hu := (complexRegularizedLogDet_upper_energy A z s hs).trans
    (add_le_add hh (le_refl ((n : ℝ)*s)))
  have hd := div_le_div_of_nonneg_right hu (Nat.cast_nonneg n)
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hB : ‖B‖^2 = (n : ℝ)*‖z‖^2 := complex_frobenius_scalar_one_sq n z
  rw [hB] at hd
  have he : (2*‖A‖^2+2*((n : ℝ)*‖z‖^2)+(n : ℝ)*s)/(n : ℝ) =
      2*(‖normalizedIidMatrix x‖^2/(n : ℝ))+2*‖z‖^2+s := by dsimp [A]; field_simp
  rw [he, normalized_frobenius_energy] at hd
  exact hd.trans (by nlinarith [pow_le_pow_left₀ (norm_nonneg z) hz 2])

lemma normalized_complexRegularizedLogDet_sq_bound {n : ℕ} (hn : 0 < n)
    (x : Fin n × Fin n → ℂ) (z : ℂ) (s R : ℝ) (hs : 0 < s) (hz : ‖z‖ ≤ R) :
    (complexRegularizedLogDet (normalizedIidMatrix x) z s/(n : ℝ))^2 ≤
      2*(|Real.log s|+2*R^2+s)^2+8*averageEntryEnergy x^2 := by
  have hl := normalized_complexRegularizedLogDet_floor hn (normalizedIidMatrix x) z s hs
  have hu := normalized_complexRegularizedLogDet_energy_bound hn x z s R hs hz
  have hQ := averageEntryEnergy_nonneg x
  let C := |Real.log s|+2*R^2+s
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have habs : |complexRegularizedLogDet (normalizedIidMatrix x) z s/(n : ℝ)| ≤ C+2*averageEntryEnergy x := by
    rw [abs_le]
    dsimp [C]
    constructor
    · linarith [neg_abs_le (Real.log s), sq_nonneg R]
    · linarith [abs_nonneg (Real.log s)]
  have hsquare := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ C+2*averageEntryEnergy x)).mpr habs
  rw [sq_abs] at hsquare
  have hcq := sq_nonneg (C-2*averageEntryEnergy x)
  change _ ≤ 2*C^2+8*averageEntryEnergy x^2
  nlinarith

#print axioms complex_frobenius_scalar_one_sq
#print axioms complexRegularizedLogDet_upper_energy
#print axioms normalized_complexRegularizedLogDet_floor
#print axioms normalized_complexRegularizedLogDet_energy_bound
#print axioms normalized_complexRegularizedLogDet_sq_bound
end SpectralRadiusUpperTail

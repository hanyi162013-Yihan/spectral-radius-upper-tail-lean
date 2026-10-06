import SpectralRadiusUpperTail.GaussianMarkedRealNormalization
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Metric
open scoped ENNReal

/-- The unit-sphere surface measure underlying the marked-eigenline
Kac--Rice normalization, in the actual Euclidean coordinate volume. -/
theorem euclidean_realSphere_surfaceArea (n : ℕ) (hn : 0 < n) :
    (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere Set.univ =
      ENNReal.ofReal
        (2 * (Real.sqrt Real.pi)^n / Real.Gamma ((n : ℝ)/2)) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hg : Real.Gamma ((n : ℝ)/2) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by positivity)).ne'
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [Measure.toSphere_apply_univ,
    EuclideanSpace.volume_ball (Fin n)
      (0 : EuclideanSpace ℝ (Fin n)) 1]
  simp only [ENNReal.ofReal_one, one_pow, one_mul, Fintype.card_fin,
    finrank_euclideanSpace]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ n)]
  congr 1
  rw [Real.Gamma_add_one (by positivity : (n : ℝ)/2 ≠ 0)]
  field_simp [hg]

#print axioms euclidean_realSphere_surfaceArea
end SpectralRadiusUpperTail

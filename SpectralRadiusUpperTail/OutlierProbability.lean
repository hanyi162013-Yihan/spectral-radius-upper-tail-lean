import SpectralRadiusUpperTail.OutlierFromIsotropic
import SpectralRadiusUpperTail.OutlierDiskParameters

namespace SpectralRadiusUpperTail
open MeasureTheory Filter Metric
open scoped Topology BigOperators Matrix

lemma outlier_probability_of_annulus_isotropic
    (Ω : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)]
    (μ : (n : ℕ) → Measure (Ω n)) [∀ n, IsFiniteMeasure (μ n)]
    (A : (n : ℕ) → Ω n → Matrix (Fin n) (Fin n) ℂ)
    (v : (n : ℕ) → Fin n → ℂ)
    (hv : ∀ n, 0 < n → (∑ i, ‖v n i‖^2) = 1)
    (b : ℂ) (d : ℝ) (hd : 0 < d) (hgap : 3*d < ‖b‖-1)
    (hiso : ∀ r L ε : ℝ, 1 < r → 0 < L → 0 < ε →
      Tendsto (fun n => (μ n).real {x | ¬ matrixAnnulusIsotropicControl (A n x)
        (v n) (v n) r L ε}) atTop (𝓝 0)) :
    Tendsto (fun n => (μ n).real {x | ¬ ∃ z ∈ closedBall b d,
      z ∈ spectrum ℂ (A n x+b • Matrix.vecMulVec (v n) (star (v n)))}) atTop (𝓝 0) := by
  obtain ⟨r,L,ε,hr,hL,hε,hbelow,habove,hsmall⟩ := outlier_disk_parameters b d hd hgap
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _ (hiso r L ε hr hL hε)
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  apply measureReal_mono (μ := μ n)
  intro x hx hi
  exact hx (outlier_of_annulus_isotropic (A n x) (v n) (hv n (by omega)) b d r L ε hd
    (by linarith) hL.le hε.le hbelow habove hsmall hi)

#print axioms outlier_probability_of_annulus_isotropic
end SpectralRadiusUpperTail

import SpectralRadiusUpperTail.ComplexFixedSetSphereAverage
import SpectralRadiusUpperTail.BoundedCoordinateSets

namespace SpectralRadiusUpperTail
open MeasureTheory Metric
open scoped ENNReal BigOperators

lemma complex_varying_set_sphere_average (n M : ℕ) (hn : 0 < n) (hMn : M ≤ n)
    (c : ℝ) (hc : 0 < c)
    (f : sphere (0 : EuclideanSpace ℂ (Fin n)) 1 → ℝ≥0∞)
    (hf : ∀ v, ∃ I : Finset (Fin n), I.card ≤ M ∧
      f v ≤ ENNReal.ofReal ((c/(c+Iᶜ.sum (fun j => ‖v.val j‖^2)))^n)) :
    (∫⁻ v, f v ∂haarSphereProbability (volume : Measure (EuclideanSpace ℂ (Fin n)))) ≤
      ENNReal.ofReal (((M+1 : ℕ) : ℝ)*((n : ℝ)+1)^M*(c/(c+1))^(n-M)) := by
  let S := boundedCoordinateSets n M
  have hr : 0 < c/(c+1) := by positivity
  have hr1 : c/(c+1) ≤ 1 := (div_le_one (by positivity : 0 < c+1)).mpr (by linarith)
  have hp : (∫⁻ v, f v ∂haarSphereProbability (volume : Measure (EuclideanSpace ℂ (Fin n)))) ≤
      ∑ I ∈ S, ENNReal.ofReal ((c/(c+1))^(n-I.card)) := by
    calc
      _ ≤ ∫⁻ v : sphere (0 : EuclideanSpace ℂ (Fin n)) 1,
          ∑ I ∈ S, ENNReal.ofReal ((c/(c+Iᶜ.sum (fun j => ‖v.val j‖^2)))^n)
          ∂haarSphereProbability (volume : Measure (EuclideanSpace ℂ (Fin n))) := by
        apply lintegral_mono
        intro v
        dsimp only
        obtain ⟨I, hI, hv⟩ := hf v
        apply hv.trans
        exact Finset.single_le_sum
          (f := fun J : Finset (Fin n) => ENNReal.ofReal ((c/(c+Jᶜ.sum (fun j => ‖v.val j‖^2)))^n))
          (fun J _ => zero_le) (show I ∈ S from (mem_boundedCoordinateSets I).mpr hI)
      _ = _ := by
        rw [lintegral_finsetSum _ (fun I _ => by fun_prop)]
        apply Finset.sum_congr rfl
        intro I _
        exact complex_fixed_set_sphere_average n hn I c hc
  have hb : (∑ I ∈ S, ENNReal.ofReal ((c/(c+1))^(n-I.card))) ≤
      (S.card : ℝ≥0∞)*ENNReal.ofReal ((c/(c+1))^(n-M)) := by
    calc
      _ ≤ ∑ _I ∈ S, ENNReal.ofReal ((c/(c+1))^(n-M)) := by
        apply Finset.sum_le_sum
        intro I hI
        apply ENNReal.ofReal_le_ofReal
        have hi := (mem_boundedCoordinateSets I).mp hI
        exact pow_le_pow_of_le_one hr.le hr1 (by omega : n-M ≤ n-I.card)
      _ = _ := by simp
  apply (hp.trans hb).trans
  have hcard : (S.card : ℝ) ≤ ((M+1 : ℕ) : ℝ)*((n : ℝ)+1)^M := by
    exact_mod_cast boundedCoordinateSets_card n M
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcard (pow_nonneg hr.le _))

#print axioms complex_varying_set_sphere_average
end SpectralRadiusUpperTail

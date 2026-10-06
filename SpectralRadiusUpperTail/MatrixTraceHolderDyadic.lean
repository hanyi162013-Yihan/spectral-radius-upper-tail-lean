import SpectralRadiusUpperTail.MatrixTraceHolderStep

namespace SpectralRadiusUpperTail
open scoped ComplexOrder Matrix
variable {𝕂 : Type*} [RCLike 𝕂] {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma matrix_trace_holder_double {m : ℕ} (hm : 0 < m)
    (h : MatrixTraceHolder 𝕂 ι m) : MatrixTraceHolder 𝕂 ι (2*m) := by
  intro L hL
  obtain ⟨P,hP,he⟩ := exists_pairedList (2*m) L hL
  have hc := h (P.map fun p => p.1*p.2) (by simpa using hP)
  have hpP : (P.map fun p => p.1*p.2).prod = L.prod := by
    rw [← pairedList_prod,he]
  rw [hpP] at hc
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ ‖L.prod.trace‖^(2*m)) hc 2
  have hprod : ((P.map fun p => matrixTraceMoment m (p.1*p.2)).prod)^2 ≤
      (P.map fun p => matrixTraceMoment (2*m) p.1*matrixTraceMoment (2*m) p.2).prod := by
    clear hP he hc hpP hs hL L
    induction P with
    | nil => simp
    | cons p P ih =>
      simp only [List.map_cons,List.prod_cons,mul_pow]
      exact mul_le_mul (matrix_trace_holder_product_step hm h p.1 p.2) ih
        (sq_nonneg _) (mul_nonneg (matrixTraceMoment_nonneg _ _) (matrixTraceMoment_nonneg _ _))
  have hc' : (‖L.prod.trace‖^(2*m))^2 ≤
      ((P.map fun p => matrixTraceMoment m (p.1*p.2)).prod)^2 := by
    simpa only [List.map_map,Function.comp_def] using hs
  calc
    _ = (‖L.prod.trace‖^(2*m))^2 := by rw [← pow_mul]; congr 1; omega
    _ ≤ _ := hc'
    _ ≤ _ := hprod
    _ = _ := by rw [← pairedList_map_prod,he]

/-- Trace Holder for every dyadic number of factors, proved by induction. -/
theorem matrix_trace_holder_dyadic (k : ℕ) : MatrixTraceHolder 𝕂 ι (2^k) := by
  induction k with
  | zero => simpa using (matrix_trace_holder_one (𝕂 := 𝕂) (ι := ι))
  | succ k ih =>
    have h := matrix_trace_holder_double (by positivity : 0 < 2^k) ih
    simpa only [pow_succ,Nat.mul_comm] using h

theorem matrix_trace_dyadic_list_bound (k : ℕ) (L : List (Matrix ι ι 𝕂))
    (hL : L.length = 2*(2^k)) :
    ‖L.prod.trace‖^(2*(2^k)) ≤ (L.map (matrixTraceMoment (2^k))).prod :=
  matrix_trace_holder_dyadic k L hL

#print axioms matrix_trace_holder_dyadic
#print axioms matrix_trace_dyadic_list_bound
end SpectralRadiusUpperTail

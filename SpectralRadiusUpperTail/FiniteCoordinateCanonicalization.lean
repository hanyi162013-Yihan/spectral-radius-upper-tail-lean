import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Piecewise

namespace SpectralRadiusUpperTail

/-- If changing each individual coordinate to its canonical representative
leaves an observable unchanged, all coordinates may be changed at once. -/
theorem finite_coordinate_canonicalization
    {ι : Type*} [Fintype ι] [DecidableEq ι] {E : ι → Type*} {V : Type*}
    (C : (i : ι) → E i → E i) (f : ((i : ι) → E i) → V)
    (h : ∀ a i, f a=f (Function.update a i (C i (a i))))
    (a : (i : ι) → E i) : f a=f (fun i => C i (a i)) := by
  classical
  have hs (s : Finset ι) : f a=f (fun i => if i ∈ s then C i (a i) else a i) := by
    induction s using Finset.induction_on with
    | empty => simp only [Finset.notMem_empty,ite_false]
    | @insert i s hi ih =>
      let b : (i : ι) → E i := fun j => if j ∈ s then C j (a j) else a j
      have he : Function.update b i (C i (b i))=
          (fun j => if j ∈ insert i s then C j (a j) else a j) := by
        funext j
        by_cases hj : j=i
        · subst j
          simp [b,hi]
        · simp [b,hj]
      exact ih.trans ((h b i).trans (congrArg f he))
  simpa using hs Finset.univ

#print axioms finite_coordinate_canonicalization
end SpectralRadiusUpperTail

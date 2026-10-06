import SpectralRadiusUpperTail.FragmentExpansion
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.List.OfFn

namespace SpectralRadiusUpperTail
open scoped BigOperators
variable {A I : Type*} [Fintype I]

lemma expandFragmentCollection_fin_count {S : ℕ} (P : Fin S → List (List (A × Bool)))
    (routes : List (List (Fin S × Bool)))
    (hperm : (routes.flatten.map Prod.fst).Perm (List.ofFn (fun i : Fin S => i))) :
    (routes.flatMap (fun toks => toks.flatMap (expandFragmentToken P))).length =
      ∑ i, (P i).length := by
  have hlen : (routes.flatMap (fun toks => toks.flatMap (expandFragmentToken P))).length =
      ((routes.flatten.map Prod.fst).map (fun i => (P i).length)).sum := by
    simp only [List.length_flatMap,List.map_map,Function.comp_def,expandFragmentToken_length,
      List.map_flatten,List.sum_flatten]
  rw [hlen,(hperm.map (fun i => (P i).length)).sum_eq]
  simp only [List.map_ofFn,List.sum_ofFn,Function.comp_def]

#print axioms expandFragmentCollection_fin_count
end SpectralRadiusUpperTail

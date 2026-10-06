import SpectralRadiusUpperTail.FragmentExpansion

namespace SpectralRadiusUpperTail
variable {A I : Type*}

lemma expandFragmentCollection_flatten (P : I → List (List (A × Bool)))
    (routes : List (List (I × Bool))) :
    (routes.flatMap (fun toks => toks.flatMap (expandFragmentToken P))).flatten =
      (routes.map (fun toks => toks.flatMap (expandSegmentToken (fun i => (P i).flatten)))).flatten := by
  induction routes with
  | nil => rfl
  | cons toks routes ih =>
    simp only [List.flatMap_cons,List.flatten_append,List.map_cons,List.flatten_cons,
      expandFragmentRoute_flatten,ih]

#print axioms expandFragmentCollection_flatten
end SpectralRadiusUpperTail

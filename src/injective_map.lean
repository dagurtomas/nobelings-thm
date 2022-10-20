import preconnected

universe u

lemma inj_to_prod (α : Type u) [topological_space α] [totally_disconnected_space α] : 
  ∃ (I : Type u), ∃ (f : α → (Π (i : I), (function.const I bool) i)), ∃ hf : continuous f, 
  function.injective f := 
begin
  let I := {fI : α → bool // continuous fI},
  use I,
  let f : α → (Π (i : I), (function.const I bool) i) := λ a i, ((coe : I → (α → bool)) i) a,
  use f, 
  split,
  { refine continuous_pi _, 
    intros i,
    cases i, assumption, },
  { intros a b hab,
    sorry, },
end
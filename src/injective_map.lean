import preconnected
import connected_discrete

universe u

lemma inj_to_prod (α : Type u) [topological_space α] [totally_separated_space α] : 
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
    let s : set α := {a, b},
    have h : ∀ fi : α → bool, continuous fi → ∀ x ∈ s, ∀ y ∈ s, fi x = fi y,
    { intros fi hfi x hx y hy,
      cases hx, cases hy, work_on_goal 1 { induction hy, induction hx, refl }, work_on_goal 1 { induction hy, induction hx, dsimp at * }, work_on_goal 2 { induction hx, cases hy, work_on_goal 1 { induction hy, dsimp at * }, work_on_goal 2 { induction hy, refl } },
      { let fi' : I := ⟨fi, hfi⟩,
        have hab' : f x fi' = f y fi' := by { rw hab },
        exact hab' },
      { let fi' : I := ⟨fi, hfi⟩,
        have hab' : f y fi' = f x fi' := by { rw hab },
        exact hab'.symm } },
    by_contra',
    have h' := exists_clopen_of_totally_separated this,
    obtain ⟨U, hU, h₁⟩ := h',
    let fi := set.bool_indicator U,
    specialize h (set.bool_indicator U) _ a _ b _,
    { exact (continuous_bool_indicator_iff_clopen U).mpr hU },
    { exact set.mem_insert a {b} },
    { exact set.mem_insert_of_mem a rfl },
    apply h₁.2,
    cases h₁, cases hU, 
    rw (set.mem_iff_bool_indicator U a) at h₁_left,
    rw h₁_left at h,
    rw set.mem_iff_bool_indicator U b,
    exact h.symm, },
end
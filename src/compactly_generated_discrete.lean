import topology.subset_properties -- compact_space
-- import topology.order -- discrete_topology
-- import topology.basic -- discrete_topology
import topology.category.Profinite.default

universe u
variable {α : Type*}
variable {β : Type*}
variables [topological_space α] -- [compactly_generated α]
variables [topological_space β] -- [compactly_generated α]


/-- the difficulty is to range (forall) over Profinite or totally_disconnected_space. Both are type classes more or less. I want to state something for all maps out of Profinites.

Question. Structure can be instance, namely `instance : topological_space (ultrafilter α) :=` 
namely ultrafilter is a structure
-/



lemma finite_range_of_compact_of_discrete [compact_space α] [discrete_topology β] (f : α → β) (hc : continuous f) : (set.range f).finite := 
--(is_compact_range hc).finite_of_discrete
-- is_compact.finite_of_discrete (is_compact_range hc)
begin
  have hf : is_compact (set.range f) := is_compact_range hc,
  apply hf.finite_of_discrete,
end

/-- attempt new -/
def is_image_of_profinite {α : Type*} [topological_space α] (s : set α) [totally_disconnected_space β] := ∃ f : β → α,  (set.range f) = s 

#check is_image_of_profinite
example {α : Type*} [topological_space α] [totally_disconnected_space β] (f : β → α) := is_image_of_profinite (set.range f) := sorry

theorem discrete_iff_finite_image_of_profinite (X : Type*) [topological_space X] : discrete_topology X ↔ (∀ (s : set X), is_image_of_profinite s → s.finite) :=
begin
  -- Profinite set is implemented as compact Hausdorff, so right direction is quick
  sorry
end

/-- hvorfor virker dette ikke?? -/
-- TODO: [compactly_generated X]
theorem discrete_iff_finite_image_of_profinite2 (X : Type*) [topological_space X] : discrete_topology X ↔ ∀ (S : Profinite.{u}) (f : S → X) (hc : continuous f), (set.range f).finite  := 
begin
  split,
  intros hd S f hc,
  -- have : compact_space S := infer_instance,
  have hf : is_compact (set.range f) := is_compact_range hc,
  exact hf.finite_of_discrete,
  -- apply finite_range_of_compact_of_discrete f hd hc,
end

/-- new attempt -/

lemma finite_image_of_profinite_of_discrete (X : Type*) [topological_space X] [discrete_topology X] : ∀ (S : Profinite.{u}) (f : S → X) (hc : continuous f), (set.range f).finite  := 
begin
  intros S f hc,
  have hf : is_compact (set.range f) := is_compact_range hc,
  exact hf.finite_of_discrete,
end


theorem discrete_iff_finite_image_of_profinite3 (X : Type*) [topological_space X] : discrete_topology X ↔ ∀ (S : Profinite.{u}) (f : S → X) (hc : continuous f), (set.range f).finite  := 
begin
  split,
  apply finite_image_of_profinite_of_discrete, 
  intro h,
  -- apply discrete_of_profinite_image_finite h,
  sorry
end


  /-- Proof strategy:
  show singletons open:
  suffices [compactly generated] for every compact space, continuous map, fiber is open: (https://ncatlab.org/nlab/show/compactly+generated+topological+space)
  K compact. admits surjection from a stone-cech compactification which is a profinite set. 
  conclude the image of K → X is finite
  So fibers comprise finite disjoint partition of K into closed sets. 
  Conclude fibers are open
 -/

 -- TODO: Can replace profinite with extremally disconnected. However don't know how to range over them (∀)
lemma discrete_of_profinite_image_finite (X : Type*) [topological_space X] : ∀ (S : Profinite.{u}) (f : S → X) (hc : continuous f), (set.range f).finite → discrete_topology X := 
begin
  intros S f hc hS,
  apply singletons_open_iff_discrete.mp,
  sorry,
end

lemma compact_rng_finite_of_profinite_image_finite (X K : Type*) [topological_space X] [topological_space K] [compact_space K] (k : K → X) : ∀ (S : Profinite.{u}) (f : S → X) (hc : continuous f), (set.range f).finite → continuous k → (set.range k).finite := 
begin
  intros S f hc hS,
  intro kc,
  -- identify image as image of map from stone cech. 
  -- discrete(K) → K cont
  -- factors through (stone-cech (discrete(K)) )
  
  sorry
end

-- NOTE: This weirdly has no name in mathlib.
-- Also, the stronger `extremally_disconnected_space (ultrafilter β)` would be nice to have?
-- see https://math.stackexchange.com/questions/3146937/stone-%C4%8Cech-compactification-is-extremally-disconnected
-- also: extremally → totally separated → totally disconnected
instance : totally_disconnected_space (ultrafilter β) := ultrafilter_totdiscon
-- instance ultra_t2 : t2_space (ultrafilter β) := ultrafilter.t2_space

-- TOOD: What's wrong???
-- instance : Profinite (ultrafilter β) := 

lemma continuous_id_of_discrete {t : topological_space α} : @continuous α α ⊥ t id :=
begin 
  apply continuous_of_discrete_topology,
end

lemma surjective_idl {α : Type*} : function.surjective (λ (x : α), x) := sorry
lemma surjective_id {α : Type*} : function.surjective (@id α) := 
-- λ x, (x, _)
begin
  intro x,
  use x,
  exact rfl,
end

lemma surjection_from_tdspace_of_compact [compact_space β] [t2_space β] :  ∃ [totally_disconnected_space α] (g : α → β), continuous g := --, function.surjective g :=
begin
  -- I don't understand `let`
  -- letI bd : topological_space β := ⊥,
  -- letI bd : compact_space β := ,
  -- haveI : discrete_topology β := ⟨rfl⟩,
  have b : totally_disconnected_space (ultrafilter β) := ultrafilter_totdiscon,
  -- `(ultrafilter.extend (id : discrete β → β))` 
  have hc : continuous (ultrafilter.extend (@id β)) := continuous_ultrafilter_extend _, --
  existsi (ultrafilter.extend (@id β)),

  -- exact ⟨ultrafilter β, b, , ⟩ 
end

-- search for lifts in mathlib 
lemma factor_through_profinite_of_map_of_compact (f : α → β) : ∃ (S : Profinite.{u}) (g : S → α) (fg : S → β), (function.surjective g) ∧ f ∘ g = fg := sorry

/--
Note: Classes/instances work as "Type classes" and types within, are "instances" of that class of types.
-/
 
def s : set nat := {111, 3}
def l : list nat := [1,2]
#check s ∪ l
#check s ∪ [(2:ℕ), 3]

def test (n : ℕ) := nat.prime n
#check test
lemma test.one (n : ℕ) (testresult : test n) : n > 1 := sorry
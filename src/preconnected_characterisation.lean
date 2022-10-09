import topology.connected
import algebra.indicator_function
import tactic.fin_cases

noncomputable theory

def Prop_to_bool : Prop → bool := λ x, x = true -- if hx : x = true then ⊤ else ⊥
def char_func {X : Type*} (U : set X) : X → Prop := λ x, x ∈ U
def char_func' {X : Type*} (U : set X) : X → bool := Prop_to_bool ∘ (char_func U) 
instance has_zero_bool : has_zero bool := ⟨⊥⟩
def cst_to_bool (X : Type*) : X → bool := λ x, ⊤

lemma indicator_continuous_iff_clopen {X : Type*} (U : set X) [topological_space X] :
  continuous (set.indicator U (cst_to_bool X)) ↔ is_clopen U :=
begin
  split,
  { sorry },
  { sorry },
end

def continuous_to_discrete {X Y : Type*} (f : X → Y) [topological_space X] : Prop := 
  ∀ y : Y, is_open (f ⁻¹' {y})

lemma continuous_to_discrete_iff_continuous {X Y : Type*} (f : X → Y) [topological_space X] [topological_space Y] [discrete_topology Y] :
  continuous_to_discrete f ↔ continuous f :=
begin
  split, swap, { exact λ hf y, continuous_def.mp hf {y} (is_open_discrete {y}) },
  refine λ hf, {is_open_preimage := _},
  intros U hU,
  have hfU : f ⁻¹' U = ⋃ y ∈ U, f ⁻¹' {y} := by tidy,
  rw hfU,
  exact is_open_bUnion (λ y hy, hf y),
end

def continuous_to_discrete_implies_constant {X Y : Type*} (α : set X) (f : X → Y) 
  [topological_space X] : Prop :=
  continuous_to_discrete f → ∀ a b : X, a ∈ α → b ∈ α → f a = f b

lemma is_preconnected_iff_continuous_to_bool_implies_constant {X : Type*} (α : set X) 
  [topological_space X] : 
  is_preconnected α ↔ ∀ f : X → bool, continuous_to_discrete_implies_constant α f :=
begin
  split,
  { sorry },
  { sorry },
end

lemma is_preconnected_iff_continuous_to_discrete_implies_constant {X : Type*} (α : set X) 
  [topological_space X] : 
  is_preconnected α ↔ ∀ Y : Type*, ∀ f : X → Y, continuous_to_discrete_implies_constant α f :=
begin
  split,
  { sorry },
  { sorry },
end
import topology.connected
import algebra.indicator_function
import tactic.fin_cases

noncomputable theory

universe u

instance disc_top_Prop : topological_space Prop := ⊥
instance disc_Prop : discrete_topology Prop := ⟨rfl⟩

def char_func {X : Type u} (U : set X) : X → Prop := λ x, x ∈ U

def Prop_to_bool : Prop → bool := λ x, x = true -- if hx : x = true then ⊤ else ⊥

def char_func' {X : Type*} (U : set X) : X → bool := Prop_to_bool ∘ (char_func U) 

def setProp : list (set Prop) := [∅, set.univ, {true}, {false}]

def set_bool : list (set bool) := [∅, set.univ, {⊤}, {⊥}]

lemma mem_set_bool (s : set bool) : s ∈ set_bool :=
begin
  by_cases ht : ⊤ ∈ s,
    by_cases hf : ⊥ ∈ s,
    { have h : s = set.univ,
      ext, split, { tauto },
      intros hx,
      by_cases hx' : x = ⊤, { rw hx', exact ht },
      { have hx'' : x = ⊥ := by tidy, rw hx'', exact hf }, 
      unfold set_bool, tidy, tauto },
    { have h : s = {⊤},
      ext, split, 
      { intros hx,
        by_cases hx' : x = ⊤, { tauto }, 
        have hx'' : x = ⊥ := by tidy, exfalso, apply hf, rw ← hx'', exact hx },
      { intros hx,
        by_cases hx' : x = ⊤, { rw hx', exact ht },
        have hx'' : x = ⊥ := by tidy, exfalso, apply hx', exact hx, },
      unfold set_bool, tidy, tauto, },
    by_cases hf : ⊥ ∈ s,
    { have h : s = {⊥},
      ext, split, 
      { intros hx,
        by_cases hx' : x = ⊤,
        { exfalso, apply ht, rw hx' at hx, exact hx },
        have hx'' : x = ⊥ := by tidy, rw hx'', tauto, },
      { intros hx,
        by_cases hx' : x = ⊤,
        { exfalso, rw hx' at hx, tauto }, 
        have hx'' : x = ⊥ := by tidy, rw hx'', exact hf, },
      unfold set_bool, tidy, tauto, },
    { have h : s = ∅,
      ext, split, swap, { tauto },
      { intros hx,
        exfalso,
        by_cases hx' : x = ⊤, 
        rw hx' at hx, apply ht, exact hx,
        have hx'' : x = ⊥ := by tidy, rw hx'' at hx, apply hf, exact hx },
      unfold set_bool, tidy, tauto },
end

lemma mem_setProp (s : set Prop) : s ∈ setProp :=
begin
  by_cases ht : true ∈ s,
    by_cases hf : false ∈ s,
    { have h : s = set.univ,
      ext, split, { tauto },
      intros hx,
      by_cases hx' : x,
      have hx'' : x = true := by tidy, rw hx'', exact ht,
      have hx'' : x = false := by tidy, rw hx'', exact hf, 
      unfold setProp, tidy, tauto, },
    { have h : s = {true},
      ext, split, 
      { intros hx,
        by_cases hx' : x,
        have hx'' : x = true := by tidy, rw hx'', tauto, 
        have hx'' : x = false := by tidy, exfalso, apply hf, rw hx'' at hx, exact hx, },
      { intros hx,
        by_cases hx' : x,
        have hx'' : x = true := by tidy, rw hx'', exact ht,
        have hx'' : x = false := by tidy, exfalso, tidy, },
      unfold setProp, tidy, tauto, },
    by_cases hf : false ∈ s,
    { have h : s = {false},
      ext, split, 
      { intros hx,
        by_cases hx' : x,
        have hx'' : x = true := by tidy, exfalso, apply ht, rw hx'' at hx, exact hx,
        have hx'' : x = false := by tidy, rw hx'', tauto, },
      { intros hx,
        by_cases hx' : x,
        have hx'' : x = true := by tidy, exfalso, tidy, 
        have hx'' : x = false := by tidy, rw hx'', exact hf, },
      unfold setProp, tidy, tauto, },
    { have h : s = ∅,
      ext, split, swap, { tauto },
      intros hx,
      exfalso,
      by_cases hx' : x, 
      have hx'' : x = true := by tidy, rw hx'' at hx, apply ht, exact hx,
      have hx'' : x = false := by tidy, rw hx'' at hx, apply hf, exact hx, 
      unfold setProp, tidy, tauto, },
end

lemma char_func_continuous {X : Type u} (U : set X) [topological_space X] : 
  continuous (char_func U) ↔ is_clopen U :=
begin
  have hUt : (char_func U) ⁻¹' {true} = U := by tidy,
  have hUf : (char_func U) ⁻¹' {false} = Uᶜ := by tidy,
  have hUX : (char_func U) ⁻¹' set.univ = set.univ := by tidy,
  have hUe : (char_func U) ⁻¹' ∅ = ∅ := by tidy,
  have h_is_clopen_true : is_clopen ({true} : set Prop) := ⟨is_open_discrete {true}, is_closed_discrete {true}⟩,
  -- let A : list (set Prop) := [∅, set.univ, {true}, {false}],
  have h_set_Prop_fin : ∀ s : set Prop, s ∈ setProp :=  λ s, mem_setProp s,
  split,
  { intros hc,
    rw ← hUt, 
    exact ⟨is_open.preimage hc h_is_clopen_true.1, is_closed.preimage hc h_is_clopen_true.2⟩, },
  { intros hU,
    refine {is_open_preimage := _},
    intros S hS,
    specialize h_set_Prop_fin S,
    fin_cases h_set_Prop_fin,
    { rw hUe, exact is_open_empty },
    { rw hUX, exact is_open_univ },
    { rw hUt, exact hU.1 },
    { rw hUf, refine is_closed.not _, exact hU.2 }, },
end

lemma preconnected_characterisation {X : Type u} [topological_space X] (α : set X) : (∀ f : α → Prop, (continuous f → ∀ a b : α, f a = f b)) → is_preconnected α :=
begin
  intros h,
  unfold is_preconnected,
  intros U V hU hV hUnion hneU hneV,
  simp at *,
  by_contra h1,
  have heUV : α ∩ (U ∩ V) = ∅,
  { tidy,
    apply h1,
    use x,
    finish },
  have h_V_in_Uc : α ∩ V ⊆ α ∩ Uᶜ,
  { tidy,
    apply h1,
    use x,
    tidy },
  have hUnion' : α = α ∩ (U ∪ V) := by tidy,
  have h_Uc_in_V : α ∩ Uᶜ ⊆ α ∩ V,
  { intros x hx,
    split, { exact hx.1 },
    by_cases hxV : x ∈ V, { exact hxV },
    exfalso,
    apply hx.2,
    have hx1 := hx.1,
    rw hUnion' at hx1,
    have hx12 := hx1.2,
    cases hx12, { exact hx12 },
    exfalso,
    apply hxV,
    exact hx12 },
  have h_V_eq_Uc : α ∩ V = α ∩ Uᶜ,
  { ext,
    split,
    intros hx,
    apply h_V_in_Uc,
    exact hx,
    intros hx,
    apply h_Uc_in_V,
    exact hx },
  have hcompl : (α.restrict U)ᶜ = (α.restrict Uᶜ) := by triv,
  have haVUc : α.restrict V = (α.restrict U)ᶜ,
  { ext, 
    split, 
    { intros hx, 
      rw hcompl, 
      have hx' : coe x ∈ α ∩ V := by tidy, 
      rw h_V_eq_Uc at hx', 
      exact hx'.2 },
    { intros hx,
      rw hcompl at hx,
      have hx' : coe x ∈ α ∩ Uᶜ := by tidy,
      rw ← h_V_eq_Uc at hx',
      exact hx'.2  } },
  have hcU : is_clopen (α.restrict U),
  { split,
    { refine is_open.preimage _ hU,
      exact continuous_subtype_val },
    { refine {is_open_compl := _},
      rw ← haVUc,
      refine is_open.preimage _ hV,
      exact continuous_subtype_val } },

  rw ← char_func_continuous (α.restrict U) at hcU,
  specialize h (char_func ((α.restrict U))),
  have habU := h hcU,
  obtain ⟨u, hu⟩ := hneU,
  obtain ⟨v, hv⟩ := hneV,
  let u' : α := ⟨u, hu.1⟩,
  let v' : α := ⟨v, hv.1⟩,
  specialize habU u' hu.1 v' hv.1,
  have hu' : char_func (α.restrict U) u' := hu.2,
  rw h_V_eq_Uc at hv,
  have hv' : v ∉ U := hv.2,
  have hv'' : ¬(char_func (α.restrict U) v') := hv',
  apply hv'',
  exact habU.1 hu',
end

lemma any_discrete {X : Type u} [topological_space X] (α : set X) (hpa : is_preconnected α) {Y : Type u} [topological_space Y] [discrete_topology Y] (f : X → Y) [continuous f] (a b : X) : a ∈ α → b ∈ α → f a = f b :=
begin
  intros ha hb,
  by_contra,
  let U := f ⁻¹' {f a},
  let V := f ⁻¹' ({f a}ᶜ),
  have hU : is_closed U,
  { refine is_closed.preimage _inst_4 _, 
    exact is_closed_discrete _ },
  have hV : is_closed V, 
  { refine is_closed.preimage _inst_4 _,
    exact is_closed_discrete _, },
  have haU : (α ∩ U).nonempty,
  { use a,
    tidy },
  have haV : (α ∩ V).nonempty,
  { use b,
    tidy },
  have haUuV : α ⊆ U ∪ V,
  { intros x hx,
    by_cases hf : f x = f a,
    { left,
      exact hf },
    { right,
      exact hf } },
  have haUV : ¬(α ∩ (U ∩ V)).nonempty := by tidy,
  apply haUV,
  exact is_preconnected_closed_iff.mp hpa U V hU hV haUuV haU haV,
end

instance has_zero_bool : has_zero bool := ⟨⊥⟩

def cst_to_bool (X : Type*) : X → bool := λ x, ⊤

variables (X : Type*) 
variables (U : set X)
#check set.indicator U (cst_to_bool X)

lemma indicator_continuous_iff_clopen {X : Type*} (U : set X) [topological_space X] :
  continuous (set.indicator U (cst_to_bool X)) ↔ is_clopen U :=
begin
  split,
  { sorry },
  { sorry },
end

def continuous_to_discrete {X Y : Type u} (f : X → Y) [topological_space X] : Prop := 
  ∀ y : Y, is_open (f ⁻¹' {y})

lemma continuous_to_discrete_iff_continuous {X Y : Type u} (f : X → Y) [topological_space X] [topological_space Y] [discrete_topology Y] :
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

lemma is_preconnected_iff_continuous_to_discrete_implies_constant {X : Type u} (α : set X) 
  [topological_space X] : 
  is_preconnected α ↔ ∀ Y : Type u, ∀ f : X → Y, continuous_to_discrete_implies_constant α f :=
begin
  split,
  { sorry },
  { sorry },
end

-- lemma preconnected_characterisation_converse {X : Type u} [topological_space X] (α : set X) [is_preconnected α] : ∀ f : X → Prop, continuous f → 

lemma connected_characterisation (X : Type u) [topological_space X] : (∀ f : X → Prop, ∀ hf : continuous f, ∀ a b : X, f a = f b) → preconnected_space X :=
begin
  intros h,
  fconstructor,
  unfold is_preconnected,
  intros U V hU hV hUnion hneU hneV,
  simp at *,
  by_contra h1,
  have heUV : U ∩ V = ∅,
  ext,
  split,
  intros hx,
  exfalso,
  apply h1,
  use x,
  exact hx,
  tauto,
  have hUnion' : U ∪ V = set.univ,
  ext,
  split,
  tauto,
  intros hx,
  apply hUnion,
  exact hx,
  have h_V_in_Uc : V ⊆ Uᶜ,
  -- ext,
  -- split,
  intros x,
  by_cases hxU : x ∈ U,
  intros hx,
  have hxe : x ∈ U ∩ V,
  split,
  exact hxU,
  exact hx,
  rw heUV at hxe,
  exfalso,
  exact hxe,
  intros hx,
  exact hxU,
  have h_Uc_in_V : Uᶜ ⊆ V,
  rw set.compl_subset_iff_union,
  exact hUnion',
  have h_V_eq_Uc : V = Uᶜ,
  ext,
  split,
  intros hx,
  apply h_V_in_Uc,
  exact hx,
  intros hx,
  apply h_Uc_in_V,
  exact hx,
  have hcU : is_clopen U,
  split,
  exact hU,
  refine {is_open_compl := _},
  rw ← h_V_eq_Uc,
  exact hV,

  rw ← char_func_continuous U at hcU,
  specialize h (char_func U),
  have habU := h hcU,
  obtain ⟨u, hu⟩ := hneU,
  obtain ⟨v, hv⟩ := hneV,
  specialize habU u v,
  have hu' : char_func U u,
  exact hu,
  rw h_V_eq_Uc at hv,
  have hv' : v ∉ U,
  exact hv,
  have hv'' : ¬(char_func U v),
  exact hv',
  apply hv'',
  exact habU.1 hu',
end
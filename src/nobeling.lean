/-
Copyright (c) 2022 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import topology.category.Profinite.as_limit
import topology.category.Top.basic
import topology.order
import preconnected 
import group_theory.free_abelian_group
import algebra.category.Group.adjunctions
import algebra.category.Group.filtered_colimits
import algebra.category.Group.biproducts
import algebra.category.Group.abelian
import algebra.category.Group.Z_Module_equivalence
import category_theory.category.ulift
import control.ulift 

-- set_option pp.universes true

universe u

variables (S : Profinite.{u})

open category_theory

instance maps_to_ab_is_ab (A : Ab.{u}) (X : Type u) : add_comm_group (X → A) :=
begin 
  exact pi.add_comm_group,
end

instance maps_to_ab_is_ab_with_top (A : Ab.{u}) (X : Top.{u}) : add_comm_group (X → A) :=
begin 
  exact pi.add_comm_group,
end

instance ab_as_top_ab_has_add (A : Ab.{u}) : has_add (Top.discrete.obj A) :=
begin
  fconstructor,
  intros a b,
  let a' : A := a,
  let b' : A := b,
  let c := a' + b',
  exact c,
end

instance ab_as_top_ab_zero_class (A : Ab.{u}) : has_zero (Top.discrete.obj A) :=
begin
  let zero : A := 0,
  fconstructor,
  exact zero,
end

lemma ab_as_top_ab_add_comm (A : Ab.{u}) : ∀ a b : (Top.discrete.obj A), a + b = b + a :=
begin
  intros a b,
  let a' : A := a,
  let b' : A := b,
  have h : a' + b' = b' + a',
  cc,
  exact h,
end

instance ab_as_top_ab_has_neg (A : Ab.{u}) : has_neg (Top.discrete.obj A) := 
begin
  fconstructor,
  intros a,
  let a' : A := a,
  let aneg : A := -(a'),
  exact aneg, 
end

instance ab_as_top_ab_has_sub (A : Ab.{u}) : has_sub (Top.discrete.obj A) :=
begin
  fconstructor,
  intros a b,
  exact a + (-b),
end

instance ab_as_top_ab_add_zero_class (A : Ab.{u}) : add_zero_class (Top.discrete.obj A) :=
begin 
  refine {  zero := 0, 
            add := begin 
              intros a b,
              exact a + b,
            end, 
            zero_add := begin 
              intros a,
              tidy,
            end, 
            add_zero := begin 
              intros a,
              tidy,
            end,
          },
end

instance ab_as_top_ab (A : Ab.{u}) : add_comm_group (Top.discrete.obj A) :=
begin
  exact AddCommGroup.add_comm_group_instance A,
end

instance maps_to_ab_is_ab_with_top_and_discrete_top (A : Ab.{u}) (X : Top.{u}) : add_comm_group (X → (Top.discrete.obj A)) :=
begin 
  exact pi.add_comm_group,
end

lemma sum_is_continuous {X : Top.{u}} {A : Ab.{u}} (f g : X ⟶ (Top.discrete.obj A)) : continuous (f + g) :=
begin
  refine continuous.add _ _,
  exact continuous_map.continuous f,
  exact continuous_map.continuous g,
end

lemma zero_is_continuous (X : Top.{u}) (A : Ab.{u}) : continuous (0 : X → (Top.discrete.obj A)) :=
begin
  exact continuous_zero,
end

lemma neg_is_continuous {X : Top.{u}} {A : Ab.{u}} (f : X ⟶ (Top.discrete.obj A)) : continuous (-f) :=
begin
  refine {is_open_preimage := _},
  intros U hU,
  let minus_U : (set (Top.discrete.obj A)) := {u | -u ∈ U},
  have h_minus_U : is_open minus_U := by triv,
  have hfU : f ⁻¹' minus_U = (-f) ⁻¹' U := by tidy,
  rw ← hfU,
  exact continuous_def.mp (continuous_map.continuous f) minus_U trivial,
end

lemma neg_is_continuous' {X : Top.{u}} {A : Ab.{u}} (f : X → (Top.discrete.obj A)) : (continuous f) → (continuous (-f)) :=
begin
  intros hf,
  refine {is_open_preimage := _},
  intros U hU,
  let minus_U : (set (Top.discrete.obj A)) := {u | -u ∈ U},
  have h_minus_U : is_open minus_U := by triv,
  have hfU : f ⁻¹' minus_U = (-f) ⁻¹' U := by tidy,
  rw ← hfU,
  exact continuous_def.mp hf minus_U trivial,
end

instance C_into_ab_is_ab (X : Top.{u}) (A : Ab.{u}) : add_comm_group (X ⟶ (Top.discrete.obj A)) :=
begin
  let incl : (X ⟶ (Top.discrete.obj A)) → (X → (Top.discrete.obj A)) := λ f, f,
  have h_incl_inj : function.injective incl := by tidy,
  have h_incl_cont : ∀ f, f ∈ set.range incl ↔ continuous f,
  { intros f,
    split,
    { intros hf,
      tidy,
      have h_hfw : incl hf_w ⁻¹' s = hf_w ⁻¹' s := by tauto,
      rw h_hfw,
      exact continuous_def.mp (continuous_map.continuous hf_w) s trivial,
    },
    { intros hf,
      tidy,
    },
  },
  let CXA : add_subgroup (X → (Top.discrete.obj A)) := 
  { carrier := set.range incl,
    add_mem' := begin
      intros f g,
      intros hf hg,
      rw h_incl_cont f at hf,
      rw h_incl_cont g at hg,
      rw h_incl_cont (f + g),
      exact continuous.add hf hg,
    end,
    zero_mem' := begin
      rw h_incl_cont 0,
      exact continuous_zero,
    end,
    neg_mem' := begin
      intros f hf,
      rw h_incl_cont f at hf,
      rw h_incl_cont (-f),
      exact neg_is_continuous' f hf,
    end,
  },
  have hCXA : add_comm_group CXA := by exact lex.add_comm_group, 
  sorry,
end

def incl_of_continuous_maps (X : Top.{u}) (A : Ab.{u}) : (X ⟶ (Top.discrete.obj A)) → (X → (Top.discrete.obj A)) := λ f, f

lemma incl_iff_cont {X : Top.{u}} {A : Ab.{u}} (f : X → (Top.discrete.obj A)) : f ∈ set.range (incl_of_continuous_maps X A) ↔ continuous f :=
begin
  split,
    { intros hf,
      tidy,
      have h_hfw : (incl_of_continuous_maps X A) hf_w ⁻¹' s = hf_w ⁻¹' s := by tauto,
      rw h_hfw,
      exact continuous_def.mp (continuous_map.continuous hf_w) s trivial,
    },
    { intros hf,
      tidy,
    },
end

def subgroup_of_continuous_maps (X : Top.{u}) (A : Ab.{u}) : add_subgroup (X → (Top.discrete.obj A)) := 
{ carrier := set.range (incl_of_continuous_maps X A),
    add_mem' := begin
      intros f g,
      intros hf hg,
      rw incl_iff_cont f at hf,
      rw incl_iff_cont g at hg,
      rw incl_iff_cont (f + g),
      exact continuous.add hf hg,
    end,
    zero_mem' := begin
      rw incl_iff_cont 0,
      exact zero_is_continuous X A,
    end,
    neg_mem' := begin
      intros f hf,
      rw incl_iff_cont f at hf,
      rw incl_iff_cont (-f),
      exact neg_is_continuous' f hf,
    end,
  } 

def ab_u_Z : Ab.{u} := ⟨ulift.{u} ℤ⟩

def ring_u_Z : Ring.{u} := ⟨ulift.{u} ℤ⟩

def CSZ (S : Profinite.{u}) : Ab.{u} := ⟨subgroup_of_continuous_maps (Profinite.to_Top.obj S) ab_u_Z⟩

def zeroone_subset : set ℤ := {0, 1}

def zeroone' : Top.{u} := Top.discrete.obj (ulift.{u} zeroone_subset) 

def zeroone : Top.{u} := Top.discrete.obj (ulift.{u} {n : ℤ | 0 ≤ n ∧ n ≤ 1}) --don't use

def zeroone_map (I : Type u) : I → Top.{u} := λ i, zeroone'

def prod01_aslimit (I : Type u) := Top.pi_fan.{u u} (zeroone_map I)

def prod01 (I : Type u) : Top.{u} := (prod01_aslimit I).X

def prod_proj {I : Type u} (i : I) : prod01 I ⟶ zeroone' :=
begin 
  let p := Top.pi_π.{u u} (zeroone_map I) i,
  have hz : zeroone' = zeroone_map I i,
  refl,
  rw hz,
  have hp : prod01 I = Top.of (Π (i : I), ↥(zeroone_map I i)),
  exact Top.pi_fan_X (zeroone_map I),
  rw hp,
  exact p,
end

lemma inj_to_prod (S : Profinite.{u}) : ∃ (I : Type u), ∃ (f : (Profinite.to_Top.obj S) ⟶ (prod01 I)), function.injective f := sorry 

def I' (S : Profinite.{u}) := (inj_to_prod S).some

-- def inj_to_prod_map (S : Profinite.{u}) : (Profinite.to_Top.obj S) ⟶ (prod01 (I S)) := {

-- },

def lambda (S : Profinite.{u}) := ordinal.type (@well_ordering_rel (I' S))

-- lemma inj_to_prod_map_existence (S : Profinite.{u}) : ∃ (f : (Profinite.to_Top.obj S) ⟶ (prod01 (I' S))), function.injective f := 
-- begin
--   have h : ∃ (I : Type u), ∃ (f : (Profinite.to_Top.obj S) ⟶ (prod01 I)), function.injective f,
--   exact inj_to_prod S,
--   obtain ⟨I, f, h1⟩ := h,
--   sorry,
--   -- have h : I = (I' S),
-- end

-- instance CSZ_ab_grp (S : Profinite.{u}) : add_comm_group (CSZ S) := by apply_instance

-- def ECSZ {S : Profinite.{u}} {I : Type u} (f : (Profinite.to_Top.obj S) ⟶ (prod01 I)) (i : I) : CSZ S :=
-- begin 
--   let pi := prod_proj i,
--   let inj : {n : ℤ | 0 ≤ n ∧ n ≤ 1} → ℤ := λ x, x,
--   let uinj : (ulift.{u} {n : ℤ | 0 ≤ n ∧ n ≤ 1}) → (ulift.{u} ℤ) := ulift.map inj,
--   let ui := Top.discrete.map uinj,
--   let elt : (Profinite.to_Top.obj S ⟶ (Top.discrete.obj ab_u_Z)) := f ≫ pi ≫ ui,
--   have h : (CSZ S).α = subgroup_of_continuous_maps (Profinite.to_Top.obj S) ab_u_Z := by refl,
--   unfold_coes,
--   rw h,
--   unfold_coes,
--   use elt,
--   unfold subgroup_of_continuous_maps,
--   have helt : ⇑elt = (incl_of_continuous_maps (Profinite.to_Top.obj S) (ab_u_Z)) elt := by refl,
--   rw helt,
--   suffices hh : incl_of_continuous_maps (Profinite.to_Top.obj S) ab_u_Z elt ∈ set.range (incl_of_continuous_maps (Profinite.to_Top.obj S) ab_u_Z),
--   exact hh,
--   tidy, 
-- end

def EC_as_map {S : Profinite.{u}} {I : Type u} (f : (Profinite.to_Top.obj S) ⟶ (prod01 I)) (i : I) :
  (Profinite.to_Top.obj S) → ring_u_Z :=
begin
  let pi : (prod01 I) → zeroone' := prod_proj i,
  let ff : (Profinite.to_Top.obj S) → (prod01 I) := f,
  let incl : zeroone_subset → ℤ := λ x, x,
  let uincl : zeroone' → ulift.{u} ℤ := ulift.map incl,
  -- let inj : {n : ℤ | 0 ≤ n ∧ n ≤ 1} → ℤ := λ x, x,
  -- let uinj : (ulift.{u} {n : ℤ | 0 ≤ n ∧ n ≤ 1}) → (ulift.{u} ℤ) := ulift.map inj,
  -- let ui := Top.discrete.map uinj,
  exact uincl ∘ pi ∘ ff,
  -- exact f ≫ pi ≫ ui,
end

lemma e_idempotent (S : Profinite.{u}) (I : Type u) : ∀ (i : I) (f : (Profinite.to_Top.obj S) ⟶ (prod01 I)) (s : (Profinite.to_Top.obj S)), 
  ((EC_as_map f i) s) * ((EC_as_map f i) s) = ((EC_as_map f i) s) :=
begin
  intros i f s,
  let ff : (Profinite.to_Top.obj S) → (prod01 I) := f,
  let pi : (prod01 I) → zeroone' := prod_proj i,
  let incl : zeroone_subset → ℤ := λ x, x,
  let uincl : zeroone' → ulift.{u} ℤ := ulift.map incl,
  -- let inj : {n : ℤ | 0 ≤ n ∧ n ≤ 1} → ℤ := λ x, x,
  -- let uinj : (ulift.{u} {n : ℤ | 0 ≤ n ∧ n ≤ 1}) → (ulift.{u} ℤ) := ulift.map inj,
  -- let ui := Top.discrete.map uinj,
  have hE : (EC_as_map f i) s = uincl (pi (ff s)) := by refl,
  have hzero : zeroone_subset = {0, 1} := by refl,
  have h01 : ∀ n : ℤ, n ∈ zeroone_subset → n = 1 ∨ n = 0,
  { intros n hn,
    exact or.swap hn,
  },
  have hincl1 : ∀ x, incl x ∈ zeroone_subset,
  { intros x,
    exact subtype.mem x,
  },
  have hincl : ∀ x, incl x = 1 ∨ incl x = 0,
  { intros x,
    -- rw hzero at x,
    apply h01 (incl x),
    exact hincl1 x,
  },
  have h : (EC_as_map f i) s = 1 ∨ (EC_as_map f i) s = 0,
  { rw hE,
    specialize hincl (ulift.down (pi (ff s))),
    cases hincl,
    left,
    apply_fun ulift.down,
    exact hincl,
    exact ulift.down_injective,
    right,
    apply_fun ulift.down,
    exact hincl,
    exact ulift.down_injective,
  },
  cases h,
  rw h,
  refl,
  rw h,
  refl,
end

def forget_ring : Ring.{u} ⥤ Ab.{u} :=
{
  obj := λ R, ⟨R⟩,
  map := 
  begin
    intros R S f,
    fconstructor,
    intros r,
    exact f r,
    simp at *,
    intros x y,
    tidy,
  end,
  map_id' := by tidy,
  map_comp' := by tidy,
}

-- def I_cst_map (I : Type u) : ℕ → Type u := λ n, I 

def prod_N (I : Type u) : Type u := Π (n : ℕ), I  

def N_order : (ℕ → ℕ → Prop) := λ n m, n ≤ m

def prod_order (I : Type u) : Π (n : ℕ), I → I → Prop := λ n, @well_ordering_rel I 

def lex_order (I : Type u) : (prod_N I) → (prod_N I) → Prop := λ x y, pi.lex N_order (prod_order I) x y 

def sub_prod (I : Type u) : Type u := 
  {x : prod_N I // (∀ n : ℕ, ordinal.typein (well_ordering_rel) (x n) ≠ 0 → (ordinal.typein (well_ordering_rel) (x n) > ordinal.typein (well_ordering_rel) (x n.succ))) ∧ 
    (∃ n : ℕ, ∀ m ≥ n, ordinal.typein (well_ordering_rel) (x m) = 0)}

def subset_prod (I : Type u) : set (prod_N I) := 
  {x : prod_N I | (∀ n : ℕ, ordinal.typein (well_ordering_rel) (x n) ≠ 0 → (ordinal.typein (well_ordering_rel) (x n) > ordinal.typein (well_ordering_rel) (x n.succ))) ∧ 
    (∃ n : ℕ, ∀ m ≥ n, ordinal.typein (well_ordering_rel) (x m) = 0)}

def Eset (S : Profinite.{u}) (I : Type u) : set (prod_N I) :=
begin
  intros x,
  sorry,
end

-- variables I : Type u
-- variables (x y : sub_prod I)
-- #check lex_order I x y


-- noncomputable def to_prod_map (S : Profinite.{u}) := (inj_to_prod_map_existence S).some 

-- variables I : Type u
-- variables i j : I
-- #check @well_ordering_rel I 
-- #check Well_order 
-- #check ordinal.type (@well_ordering_rel I)
-- The type I'm checking above is I as an ordinal (by the well-ordering theorem). 

theorem CSZ_is_free (S : Profinite.{u}) : ∃ (I : Type u) (f : (AddCommGroup.of (subgroup_of_continuous_maps (Profinite.to_Top.obj S) ab_u_Z)) ⟶ AddCommGroup.of (free_abelian_group I)), is_iso f := 
begin
  sorry,
end

theorem CSZ_is_free' (S : Profinite.{u}) : ∃ (I : Type u) (f : AddCommGroup.of ((Profinite.to_Top.obj S) ⟶ (Top.discrete.obj ab_u_Z)) ⟶ AddCommGroup.of (free_abelian_group I)), is_iso f := 
begin
  sorry,
end

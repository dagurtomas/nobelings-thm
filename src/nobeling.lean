/-
Copyright (c) 2022 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import topology.category.Profinite.as_limit
import topology.category.Top.basic
import topology.order
import group_theory.free_abelian_group
import algebra.category.Group.adjunctions
import algebra.category.Group.filtered_colimits
import algebra.category.Group.biproducts
import algebra.category.Group.abelian
import algebra.category.Group.Z_Module_equivalence
import category_theory.category.ulift

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

theorem CSZ_is_free (S : Profinite.{u}) : ∃ (I : Type u) (f : (AddCommGroup.of (subgroup_of_continuous_maps (Profinite.to_Top.obj S) ab_u_Z)) ⟶ AddCommGroup.of (free_abelian_group I)), is_iso f := 
begin
  sorry,
end

theorem CSZ_is_free' (S : Profinite.{u}) : ∃ (I : Type u) (f : AddCommGroup.of ((Profinite.to_Top.obj S) ⟶ (Top.discrete.obj ab_u_Z)) ⟶ AddCommGroup.of (free_abelian_group I)), is_iso f := 
begin
  sorry,
end

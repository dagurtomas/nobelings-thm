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

instance ab_as_top_ab (A : Ab.{u}) : has_add (Top.discrete.obj A) :=
begin
  fconstructor,
  intros a b,
  let a' : A := a,
  let b' : A := b,
  let c := a' + b',
  exact c,
end

def ab_u_Z : Ab.{u} := ⟨ulift.{u} ℤ⟩

instance C_into_ab_is_ab (X : Top.{u}) (A : Ab.{u}) : add_comm_group (X ⟶ (Top.discrete.obj A)) :=
begin
  sorry,
end

theorem CSZ_is_free (S : Profinite.{u}) : ∃ (I : Type u) (f : AddCommGroup.of ((Profinite.to_Top.obj S) ⟶ (Top.discrete.obj ab_u_Z)) ⟶ AddCommGroup.of (free_abelian_group I)), is_iso f := 
begin
  sorry,
end

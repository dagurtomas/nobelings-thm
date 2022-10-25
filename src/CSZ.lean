import topology.category.Profinite.default
import injective_map
import algebra.free_algebra
import data.finset.basic
import group_theory.free_abelian_group

noncomputable theory

universe u

def bool_to_Z : bool → ℤ := λ x, ite (x = tt) 1 0

instance totally_separated_of_profinite (S : Profinite.{u}) : totally_separated_space S :=
  totally_separated_of_totally_disconnected_compact_hausdorff S
  
def I (S : Profinite.{u}) : Type u := 
  {fI : S → bool // continuous fI}

def inj_map (S : Profinite.{u}) : S → ((I S) → bool) :=
  map_to_I' S

def CSZ (S : Profinite.{u}) : Type u := {f : S → ℤ // continuous f}

instance ring_SZ (S : Profinite.{u}) : comm_ring (S → ℤ) := pi.comm_ring

def subring_CSZ (S : Profinite.{u}) : subring (S → ℤ) := 
{ carrier := {f : S → ℤ | continuous f},
  zero_mem' := begin
    simp only [set.mem_set_of_eq],
    refine continuous_def.mpr _,
    intros s hs,
    by_cases hzero : (0 : ℤ) ∈ s,
    { have : (0 ⁻¹' s : set S) = set.univ, 
      { ext1, 
        simp only [set.mem_preimage, set.mem_univ, pi.zero_apply, iff_true], 
        assumption },
      rw this,
      exact is_open_univ, },
    { have : (0 ⁻¹' s : set S) = ∅, 
      { ext1, 
        simp only [set.mem_preimage, pi.zero_apply],
        rw ← not_iff_not,
        split, tauto, exact λ h, hzero, },
      rw this,
      exact is_open_empty, },
  end,
  one_mem' := begin
    simp only [set.mem_set_of_eq],
    refine continuous_def.mpr _,
    intros s hs,
    by_cases hzero : (1 : ℤ) ∈ s,
    { have : (1 ⁻¹' s : set S) = set.univ, 
      { ext1, 
        simp only [set.mem_preimage, set.mem_univ, pi.zero_apply, iff_true], 
        assumption },
      rw this,
      exact is_open_univ, },
    { have : (1 ⁻¹' s : set S) = ∅, 
      { ext1, 
        simp only [set.mem_preimage, pi.zero_apply],
        rw ← not_iff_not,
        split, tauto, exact λ h, hzero, },
      rw this,
      exact is_open_empty, },
  end,
  add_mem' := λ f g hf hg, continuous.add hf hg,
  mul_mem' := λ f g hf hg, continuous.mul hf hg,
  neg_mem' := λ f hf, continuous.neg hf,
}

instance ring_CSZ (S : Profinite.{u}) : comm_ring (CSZ S) := (subring_CSZ S).to_comm_ring

instance alg_CSZ (S : Profinite.{u}) : algebra ℤ (CSZ S) := algebra_int (CSZ S)

def prod_N (I : Type u) : Type u := Π (n : ℕ), I  

def N_order : (ℕ → ℕ → Prop) := λ n m, n ≤ m

def prod_order (I : Type u) : Π (n : ℕ), I → I → Prop := λ n, @well_ordering_rel I 

def lex_order (I : Type u) : (prod_N I) → (prod_N I) → Prop := 
  λ x y, pi.lex N_order (prod_order I) x y 

def sub_prod (I : Type u) : Type u := 
  {x : prod_N I // (∀ n : ℕ, ordinal.typein (well_ordering_rel) (x n) ≠ 0 → 
    (ordinal.typein (well_ordering_rel) (x n) > ordinal.typein (well_ordering_rel) (x n.succ))) ∧ 
    (∀ n : ℕ, (ordinal.typein (well_ordering_rel) (x n) ≥ ordinal.typein (well_ordering_rel) (x n.succ))) ∧ 
    {n : ℕ | ordinal.typein (well_ordering_rel) (x n) > 0}.finite }

  -- (∀ n : ℕ, ordinal.typein (well_ordering_rel) (x n) ≠ 0 → 
  -- (ordinal.typein (well_ordering_rel) (x n) > ordinal.typein (well_ordering_rel) (x n.succ))) ∧ 
  -- (∃ n : ℕ, ∀ m ≥ n, ordinal.typein (well_ordering_rel) (x m) = 0)

def subset_prod (I : Type u) : set (prod_N I) := 
  {x : prod_N I | (∀ n : ℕ, ordinal.typein (well_ordering_rel) (x n) ≠ 0 → 
    (ordinal.typein (well_ordering_rel) (x n) > ordinal.typein (well_ordering_rel) (x n.succ))) ∧ 
    (∀ n : ℕ, (ordinal.typein (well_ordering_rel) (x n) ≥ ordinal.typein (well_ordering_rel) (x n.succ))) ∧ 
    {n : ℕ | ordinal.typein (well_ordering_rel) (x n) > 0}.finite }

--(∃ n : ℕ, ordinal.typein (well_ordering_rel) (x n) = 0)

instance decidable_eq_IS (S : Profinite.{u}) : decidable_eq (I S) := classical.dec_eq _

def e_indices {I : Type u} (L : sub_prod I) [decidable_eq I] : finset I := 
  finset.image L.val (set.finite.to_finset L.property.2.2)

def e_cont {S : Profinite.{u}} (i : I S) : 
  continuous (bool_to_Z ∘ (λ ι : (I S → bool), ι i) ∘ map_to_I' S) := 
  continuous_bot.comp ((continuous_apply i).comp (inj_to_prod' S).1)

def e {S : Profinite.{u}} (i : I S) : CSZ S := 
  ⟨bool_to_Z ∘ (λ ι : (I S → bool), ι i) ∘ map_to_I' S, e_cont i⟩

def prod_e {S : Profinite.{u}} (L : sub_prod (I S)) : CSZ S := finset.prod (e_indices L) e 

def Eset (S : Profinite.{u}) : set (sub_prod (I S)) := {L : sub_prod (I S) | ∀ s : finset (sub_prod (I S)), 
  (∀ L' : sub_prod (I S), L' ∈ s → (lex_order (I S)) L'.val L.val) → finset.sum s prod_e ≠ prod_e L}

noncomputable theorem nobelings_thm (S : Profinite.{u}) : CSZ S ≅ free_abelian_group (Eset S) := sorry 

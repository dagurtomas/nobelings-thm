import topology.category.Profinite.default
import injective_map
import algebra.free_algebra

universe u

instance totally_separated_of_profinite (S : Profinite.{u}) : totally_separated_space S :=
  totally_separated_of_totally_disconnected_compact_hausdorff S
  
def I (S : Profinite.{u}) : Type u := 
  {fI : S → bool // continuous fI}

def inj_map (S : Profinite.{u}) : S → ((I S) → bool) :=
  map_to_I' S

def CSZ (S : Profinite.{u}) : Type u := {f : S → ℤ // continuous f}

instance ring_CSZ (S : Profinite.{u}) : ring (CSZ S) := sorry

instance alg_CSZ (S : Profinite.{u}) : algebra ℤ (CSZ S) := sorry

def prod_N (I : Type u) : Type u := Π (n : ℕ), I  

def N_order : (ℕ → ℕ → Prop) := λ n m, n ≤ m

def prod_order (I : Type u) : Π (n : ℕ), I → I → Prop := λ n, @well_ordering_rel I 

def lex_order (I : Type u) : (prod_N I) → (prod_N I) → Prop := λ x y, pi.lex N_order (prod_order I) x y 

def sub_prod (I : Type u) : Type u := 
  {x : prod_N I // (∀ n : ℕ, ordinal.typein (well_ordering_rel) (x n) ≠ 0 → 
    (ordinal.typein (well_ordering_rel) (x n) > ordinal.typein (well_ordering_rel) (x n.succ))) ∧ 
    (∃ n : ℕ, ∀ m ≥ n, ordinal.typein (well_ordering_rel) (x m) = 0)}

def subset_prod (I : Type u) : set (prod_N I) := 
  {x : prod_N I | (∀ n : ℕ, ordinal.typein (well_ordering_rel) (x n) ≠ 0 → 
    (ordinal.typein (well_ordering_rel) (x n) > ordinal.typein (well_ordering_rel) (x n.succ))) ∧ 
    (∃ n : ℕ, ∀ m ≥ n, ordinal.typein (well_ordering_rel) (x m) = 0)}

def e (S : Profinite.{u}) : I S → CSZ S := sorry 
  -- corresponding projection, compose with the map: bool → ℤ, ff mapsto 0, tt mapsto 1

def prod_e (S : Profinite.{u}) : sub_prod (I S) → CSZ S := sorry 
  -- product of the e i for i ∈ sub_prod (I S), where e 0 = 1

def Eset (S : Profinite.{u}) (I : Type u) : set (prod_N I) := sorry 
  -- subset satisfying property of not being a linear combination of smaller e_prod's

noncomputable theorem nobelings_thm (S : Profinite.{u}) : CSZ S ≅ free_algebra ℤ (Eset S (I S)) := sorry 

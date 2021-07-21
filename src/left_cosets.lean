import group_theory.group_action
import tactic

universes u v w
variables {G : Type u} {α : Type v} {β : Type w} [group G]

open_locale coset

abbreviation left_cosets (L : subgroup G) : Type* := 
{ S : set G // ∃ g : G, g *l L = S }

namespace left_cosets

variables {L : subgroup G}

@[simps] def smul (g : G) (s : left_cosets L) : left_cosets L :=
⟨g *l s.1, begin
  rcases s with ⟨_, g', rfl⟩,
  simp [left_coset_assoc],
end⟩

/-- Use notation • for smul -/
instance : has_scalar G (left_cosets L) := ⟨smul⟩

/-- Use notation ∈ for is an element of -/
instance : set_like (left_cosets L) G := 
{ coe := subtype.val,
  coe_injective' := subtype.coe_injective }

@[ext] theorem ext {p q : left_cosets L} (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q := 
set_like.ext h

lemma mem_smul (g h : G) (s : left_cosets L) : h ∈ g • s ↔ g⁻¹ * h ∈ s :=
by simp [(•), ← set_like.mem_coe, left_coset]

def aux_action : mul_action G (left_cosets L) :=
{ smul := (•),
  one_smul := begin
    intro t,
    ext,
    rw mem_smul,
    simp,
  end,
  mul_smul := begin
    intros t u v,
    ext,
    simp only [mem_smul],
    congr' 2,
    group,
end }

end left_cosets

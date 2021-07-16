/- Need to check how many of these I'm actually using -/
import group_theory.group_action
import group_theory.group_action.basic
import group_theory.quotient_group
import group_theory.order_of_element
import data.zmod.basic
import data.fintype.card
import data.list.rotate
import algebra.group.conj
import group_theory.sylow
import tactic


open equiv fintype finset mul_action function nat sylow
open subgroup quotient_group
open_locale big_operators
universes u v w
variables {G : Type u} {α : Type v} {β : Type w} [group G]

local attribute [instance, priority 10] subtype.fintype set_fintype classical.prop_decidable

/-- Useful standard library functions
quotient L - set of all left cosets
conjugates, is_conj
p.prime - predicate
-/


def is_sylow_subgroup [fintype G] (L : subgroup G) {p m n : ℕ} (hp : p.prime)
(hG : card G = p ^ n * m) (hndiv: ¬ p ∣ m) :=
  card L = p ^ n

namespace is_sylow_subgroup
variables [fintype G] {L : subgroup G} {p m n : ℕ} {hp : p.prime}
{hG : card G = p ^ n * m} {hndiv: ¬ p ∣ m} (h : is_sylow_subgroup L hp hG hndiv)

end is_sylow_subgroup

lemma is_sylow_subgroup_def [fintype G] (L : subgroup G) {p m n : ℕ} (hp : p.prime)
(hG : card G = p ^ n * m) (hndiv: ¬ p ∣ m) : is_sylow_subgroup L hp hG hndiv ↔ (card L = p ^ n)
:= iff.rfl

def conjugate_subgroup (L : subgroup G) (g : G) : subgroup G :=
{ carrier := { c | ∃ h ∈ L, c = g⁻¹ * h * g },
  one_mem' := 
begin
  use 1,
  split,
  exact one_mem L,
  simp,  
end,
  mul_mem' := 
begin
  rintros - - ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩,
  exact ⟨c * d, L.mul_mem hc hd, by group⟩,
end,
  inv_mem' := 
begin
  simp,
  intros x y hy hx,
  use (g * x * g⁻¹)⁻¹,
  split,
  {
    rw [hx, mul_assoc, mul_assoc, mul_assoc, mul_inv_self, mul_one, ← mul_assoc, mul_inv_self, one_mul],
    exact inv_mem L hy,
  },
  simp,
  rw [mul_assoc, mul_assoc, mul_assoc, inv_mul_self, mul_one, ← mul_assoc, inv_mul_self],
  simp,
end }


def subgroups_conj_by_x (L K : subgroup G) (x : G) :=
  conjugate_subgroup L x = K

lemma subgroups_conj_by_x_def (L K : subgroup G) (x : G) : 
  conjugate_subgroup L x = K ↔ subgroups_conj_by_x L K x := iff.rfl

def subgroups_are_conj (L K : subgroup G) := 
  ∃ g : G, subgroups_conj_by_x L K g

def set_of_sylow_subgroups [fintype G] {p m n : ℕ} (hp : p.prime) (hG : card G = p ^ n * m) 
  (hndiv: ¬ p ∣ m) : set (subgroup G) :=
  { L | is_sylow_subgroup L hp hG hndiv }

-- def set_of_conjug_subgroups [fintype G] (L : subgroup G) : set (subgroup G) :=
--   { J | subgroups_are_conj L J ∧ ∃ p : ℕ, is_sylow_subgroup J p }

noncomputable def index_of_subgroup [fintype G] (L : subgroup G) : ℕ :=
  card G / card L

lemma index_of_subgroup_def [fintype G] (L : subgroup G) : 
  index_of_subgroup L = card G / card L := rfl
 
lemma card_subgroup_pos [fintype G] (L : subgroup G) : 0 < card L :=
card_pos_iff.2 $ nonempty.intro ⟨1, L.one_mem⟩

-- lagranges theorem
lemma index_of_subgroup_def2 [fintype G] (L : subgroup G) :
  index_of_subgroup L = card (quotient L) := 
begin
  rw [index_of_subgroup_def, card_eq_card_quotient_mul_card_subgroup L],
  rw [nat.mul_div_assoc _ (dvd_refl (card ↥L)), nat.div_self (card_subgroup_pos L)],
  simp,
end

-- this is my previous h₃ and h₄ combined
-- h₃ : ¬ p ∣ index_of_subgroup L,
-- h₄ : ¬ index_of_subgroup L ≡ 0 [MOD p]
lemma subgroup_index_not_conj_zero_wrt_p [fintype G] {L : subgroup G} {p m n : ℕ}
(hp : p.prime) (hG : card G = p ^ n * m) (hndiv: ¬ p ∣ m) (h : is_sylow_subgroup L hp hG hndiv) 
  : ¬ index_of_subgroup L ≡ 0 [MOD p] :=
begin
  intro hn,
  rw [nat.modeq.modeq_zero_iff, index_of_subgroup, hG] at hn,
  rw is_sylow_subgroup_def at h,
  rw [h, mul_comm, nat.mul_div_cancel _ (pow_pos (pos_of_gt hp.left) n)] at hn,
  apply hndiv,
  exact hn,
end

-- useful
-- use modeq.mod_modeq and transitivity to change between % notation and [MOD] notation
-- pow_div := p ^ n / p ^ m = p ^ (n - m)
-- to prove prime is greater than 0 : exact pos_of_gt hp.left

/-- Formulation of second sylow theorem -/
-- Alternative definition would be set_of_conjug_subgroups L = set_of_sylow_subgroups p
-- from kbuzzards group theory game

-- in mul_action A B, A is the group and B is the set where B -> f(B)
-- i have K acting on quotient L


theorem sylow_two [fintype G] {p n m : ℕ} [fintype G] (L K : subgroup G) {p m n : ℕ} 
(hp : p.prime) (hG : card G = p ^ n * m) (hndiv: ¬ p ∣ m) [mul_action K (quotient L)]
( h₁ : is_sylow_subgroup L hp hG hndiv) (h₂ : is_sylow_subgroup K hp hG hndiv)
 : subgroups_are_conj K L :=
begin
  haveI : fact (p.prime) := ⟨ hp ⟩,
  -- this is my lemma, used in h₅
  have h₃ : ¬ index_of_subgroup L ≡ 0 [MOD p], {
    intro hn,
    rw [nat.modeq.modeq_zero_iff, index_of_subgroup, hG] at hn,
    rw is_sylow_subgroup_def at h₁,
    rw [h₁, mul_comm, nat.mul_div_cancel _ (pow_pos (pos_of_gt hp.left) n)] at hn,
    apply hndiv,
    exact hn,
  },
  have h₄ : index_of_subgroup L ≡ card (fixed_points K (quotient L)) [MOD p], {
    rw is_sylow_subgroup_def at h₂,
    rw index_of_subgroup_def2,
    exact card_modeq_card_fixed_points p h₂,
  },
  -- previously found a card lemma that says ≠ 0 iff ∃ statement
  have h₅ : 0 < card (fixed_points K (quotient L)), {
    apply lt_of_le_of_ne _ _, {
      exact le_of_not_gt (card ↥(fixed_points ↥K (quotient L))).not_lt_zero,
    }, {
      intro hn,
      apply subgroup_index_not_conj_zero_wrt_p hp hG hndiv h₁,
      rw hn,
      exact h₄,
      -- alternatively use card_ne_zero_of_mem, and a proof that there is at least one 
      -- fixed point
    },
  },
  have h₆ : ∃ x : G, (conjugate_subgroup K x) ≤ L, {
    rw card_pos_iff at h₅,
    apply nonempty.elim h₅,
    rintro ⟨fp, hfp⟩,
    rw mul_action.mem_fixed_points at hfp,
    --do i need orbit stabiliser theorem for this?
    -- fp is a left coset so of form xK. I need to extract x
  
    -- need to extract an x from fixed_points K st 

  -- let xH ∈ K'
  -- then yxH = xH, ∀ y ∈ K     so x⁻¹yxH = L, ∀ y ∈ K -- this is my aux_lemma
  -- so x⁻¹Hx ≤ K -- this is theorem h₄
    sorry,
  },
  have h₇ : ∀ x : G, fintype.card (conjugate_subgroup K x) = card K, {
    rw is_sylow_subgroup_def at h₁ h₂,
    intro x,
    rw [h₂, h₁.symm],
    rw card_eq,
    apply nonempty.intro,
    
    sorry,
  },
  have h₈ : ∃ x : G, ( (conjugate_subgroup K x) = L), {
    apply exists.elim h₆,
    intros g hx,
    use g,
    
    -- type problem - wants to unify (conjugate_subgroup K x) and top
    -- apply subgroup.eq_top_of_card_eq _ _,

    -- combine h₆ and h₇ and bam
    sorry,
  },
  -- remove h₈ and make it part of this proof
  rw subgroups_are_conj,
  unfold subgroups_conj_by_x,
  -- rw ← subgroups_conj_by_x_def, -- says can't find instance of pattern?
  exact h₈,

  -- let L' be the set of left cosets of L
  -- let K act on L' by y(xH) = (yx)L, y ∈ K, (x is forming the coset from L to L')

  -- let xH ∈ K'
  -- then yxH = xH, ∀ y ∈ K     so x⁻¹yxH = L, ∀ y ∈ K -- this is my aux_lemma
  -- so x⁻¹Hx ≤ K -- this is theorem h₄
  -- since |L| = |K|, |x⁻¹Hx| = |K|, so x⁻¹Hx = K so are conjugate subgroups

  sorry,
end

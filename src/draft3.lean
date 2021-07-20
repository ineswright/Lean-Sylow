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

-- local attribute [instance, priority 10] subtype.fintype set_fintype classical.prop_decidable
open_locale classical

def is_sylow_subgroup [fintype G] (L : subgroup G) {p m n : ℕ} (hp : p.prime)
(hG : card G = p ^ n * m) (hndiv: ¬ p ∣ m) :=
  card L = p ^ n

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
  -- come back to this it should only be a few lines
  -- using simp and not closing a goal is bad
  simp only [and_imp, exists_prop, set.mem_set_of_eq, exists_imp_distrib],
  intros x y hy hx,
  use (g * x * g⁻¹)⁻¹,
  split,
  {
    rw [hx, mul_assoc, mul_assoc, mul_assoc, mul_inv_self, mul_one, ← mul_assoc, mul_inv_self, one_mul],
    exact inv_mem L hy,
  },
  group,
end }


def subgroups_conj_by_x (L K : subgroup G) (x : G) :=
  conjugate_subgroup L x = K

lemma subgroups_conj_by_x_def (L K : subgroup G) (x : G) : 
   subgroups_conj_by_x L K x ↔ conjugate_subgroup L x = K := iff.rfl

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

-- splitting into two 3 line lemmas is more readable
-- this is my previous h₃ and h₄ combined
-- h₃ : ¬ p ∣ index_of_subgroup L,
-- h₄ : ¬ index_of_subgroup L ≡ 0 [MOD p]

lemma subgroup_index_equal [fintype G] {L : subgroup G} {p m n : ℕ}
(hp : p.prime) (hG : card G = p ^ n * m) (hndiv: ¬ p ∣ m) (h : is_sylow_subgroup L hp hG hndiv) 
  : index_of_subgroup L = m :=
begin
  rw is_sylow_subgroup_def at h,
  rw [index_of_subgroup_def, hG, h, nat.mul_div_cancel_left _ (pow_pos (pos_of_gt hp.left) n)],
end

lemma subgroup_index_not_conj_zero_wrt_p [fintype G] {L : subgroup G} {p m n : ℕ}
(hp : p.prime) (hG : card G = p ^ n * m) (hndiv: ¬ p ∣ m) (h : is_sylow_subgroup L hp hG hndiv) 
  : ¬ index_of_subgroup L ≡ 0 [MOD p] :=
begin
  rw subgroup_index_equal hp hG hndiv h,
  intro hn,
  apply hndiv,
  exact modeq.modeq_zero_iff.mp hn,
end


open_locale coset

def left_cosets (L : subgroup G) : set (set G) := 
set.range (λ g, g *l (L : set G))

def left_cosets'(L : subgroup G) : set (set G) := 
{ S : set G | ∃ g : G, g *l L = S }

lemma left_cosets'_def (L : subgroup G) :
  left_cosets' L = { S : set G | ∃ g : G, g *l L = S } := rfl

lemma left_cosets_def_equal (L : subgroup G) :
  left_cosets L = left_cosets' L := rfl

namespace left_cosets

variables (L : subgroup G)

def left_cosets.smul (g : G) (s : left_cosets L) : left_cosets L :=
⟨g *l s.1, begin
  rcases s with ⟨_, g', rfl⟩,
  simp [left_coset_assoc, left_cosets_def_equal, left_cosets'_def],
end⟩


def aux_action (g : G) (s : left_cosets L) : mul_action G (left_cosets L) :=
{ smul := left_cosets.smul _,
  one_smul := begin
    intro t,
    sorry,
  end,
  mul_smul := begin
    intros t u v,
    sorry,
  end }

theorem sylow_two [fintype G] {p n m : ℕ} [fintype G] (L K : subgroup G) {p m n : ℕ} 
(hp : p.prime) (hG : card G = p ^ n * m) (hndiv: ¬ p ∣ m)
( h₁ : is_sylow_subgroup L hp hG hndiv) (h₂ : is_sylow_subgroup K hp hG hndiv)
 : subgroups_are_conj K L :=
begin
  haveI : fact (p.prime) := ⟨ hp ⟩,
  -- this is my lemma, used in h₅
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
    rcases h₅ with ⟨fp, hfp⟩,
    rw mul_action.mem_fixed_points at hfp,
    let a := quotient.out' fp,
    
    -- apply induction_on fp,
    -- intro g,
    -- use g,
    
    -- unfold quotient_group.quotient at fp,
    -- unfold left_rel at fp,

    -- rw ← mem_stabilizer_iff at hfp, -- after extracting x from hfp
  
    --do i need orbit stabiliser theorem for this?
    -- fp is a left coset so of form xK. I need to extract x
  
    -- need to extract an x from fixed_points K st 

  -- let xH ∈ K'
  -- then yxH = xH, ∀ y ∈ K     so x⁻¹yxH = L, ∀ y ∈ K
  -- so x⁻¹Hx ≤ K
    sorry,
  },
  have h₇ : ∀ x : G, card (conjugate_subgroup K x) = card L, {
    rw is_sylow_subgroup_def at h₁ h₂,
    intro x,
    -- rw [h₂, h₁.symm],
    -- rw card_eq,
    -- apply nonempty.intro,

    -- then need to construct a bijection between K and conjugate_subgroup K x
    -- bijection is given by f(k) = x⁻¹kx
    sorry,
  },
  have h₈ : ∃ x : G, ( (conjugate_subgroup K x) = L), {
    apply exists.elim h₆,
    intros g hx,
    use g,
    
    -- type problem - wants to unify (conjugate_subgroup K x) and top

    -- combine h₆ and h₇ and bam
    sorry,
  },
  -- remove h₈ and make it part of this proof
  rw subgroups_are_conj,
  unfold subgroups_conj_by_x,
  -- rw subgroups_conj_by_x_def, -- says can't find instance of pattern?
  exact h₈,

  -- let L' be the set of left cosets of L
  -- let K act on L' by y(xL) = (yx)L, y ∈ K, (x is forming the coset from L to L')

  -- let xH ∈ K'
  -- then yxH = xH, ∀ y ∈ K     so x⁻¹yxH = L, ∀ y ∈ K -- this is my aux_lemma
  -- so x⁻¹Hx ≤ K -- this is theorem h₄
  -- since |L| = |K|, |x⁻¹Hx| = |K|, so x⁻¹Hx = K so are conjugate subgroups
end

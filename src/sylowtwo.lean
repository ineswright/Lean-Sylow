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
import left_cosets

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

-- TODO: simplify proofs to a few lines
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

theorem sylow_two [fintype G] {p n m : ℕ} (L K : subgroup G) 
(hp : p.prime) (hG : card G = p ^ n * m) (hndiv: ¬ p ∣ m)
( h₁ : is_sylow_subgroup L hp hG hndiv) (h₂ : is_sylow_subgroup K hp hG hndiv)
-- (ha : left_cosets.aux_action) 
: subgroups_are_conj K L :=
begin
  haveI : fact (p.prime) := ⟨ hp ⟩,
  have h₄ : index_of_subgroup L ≡ card (fixed_points K (quotient L)) [MOD p], {
    rw is_sylow_subgroup_def at h₂,
    rw index_of_subgroup_def2,
    exact card_modeq_card_fixed_points p h₂,
  },
  have h₅ : 0 < card (fixed_points K (quotient L)), {
    apply lt_of_le_of_ne _ _, {
      exact le_of_not_gt (card ↥(fixed_points ↥K (quotient L))).not_lt_zero,
    }, {
      intro hn,
      apply subgroup_index_not_conj_zero_wrt_p hp hG hndiv h₁,
      rw hn,
      exact h₄,
    },
  },
  have h₆ : ∃ x : G, (conjugate_subgroup K x) ≤ L, {
    rw card_pos_iff at h₅,
    rcases h₅ with ⟨fp, hfp⟩,
    rw mul_action.mem_fixed_points at hfp,
    let a := quotient.out' fp,
    use a,
  
    -- need to extract an x from fixed_points K st 

  -- let xH ∈ K'
  -- then yxH = xH, ∀ y ∈ K     so x⁻¹yxH = L, ∀ y ∈ K
  -- so x⁻¹Hx ≤ K
    sorry,
  },
  have h₇ : ∀ x : G, card (conjugate_subgroup K x) = card L, {
    rw is_sylow_subgroup_def at h₁ h₂,
    intro x,
    rw [h₁, h₂.symm],
    

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
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
quotient H - set of all left cosets
conjugates, is_conj
p.prime - predicate

-/

-- concerned no mention of p.prime - Ines
-- by KBuzzard
def is_sylow_subgroup [fintype G] (H : subgroup G) {p m n : ℕ} (hp : p.prime)
(hG : card G = p ^ n * m) (hndiv: ¬ p ∣ m) :=
  card H = p ^ n

namespace is_sylow_subgroup
variables [fintype G] {H : subgroup G} {p m n : ℕ} {hp : p.prime}
{hG : card G = p ^ n * m} {hndiv: ¬ p ∣ m} (h : is_sylow_subgroup H hp hG hndiv)

-- need a def card H lemma here so i can use rw instead of unfold

end is_sylow_subgroup


def conjugate_subgroup (H : subgroup G) (g : G) : subgroup G :=
{ carrier := { c | ∃ h ∈ H, c = g⁻¹ * h * g },
  one_mem' := 
begin
  use 1,
  split,
  exact one_mem H,
  simp,  
end,
  mul_mem' := 
begin
  rintros - - ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩,
  exact ⟨c * d, H.mul_mem hc hd, by group⟩,
end,
  inv_mem' := 
begin
  simp,
  intros x y hy hx,
  use (g * x * g⁻¹)⁻¹,
  split,
  {
    rw [hx, mul_assoc, mul_assoc, mul_assoc, mul_inv_self, mul_one, ← mul_assoc, mul_inv_self, one_mul],
    exact inv_mem H hy,
  },
  simp,
  rw [mul_assoc, mul_assoc, mul_assoc, inv_mul_self, mul_one, ← mul_assoc, inv_mul_self],
  simp,
end }


def subgroups_are_conj_by_x (H K : subgroup G) (x : G) :=
  conjugate_subgroup H x = K

def subgroups_are_conj (H K : subgroup G) := 
  ∃ g : G, subgroups_are_conj_by_x H K g

def set_of_sylow_subgroups [fintype G] {p m n : ℕ} (hp : p.prime) (hG : card G = p ^ n * m) 
  (hndiv: ¬ p ∣ m) : set (subgroup G) :=
  { H | is_sylow_subgroup H hp hG hndiv }

-- def set_of_conjug_subgroups [fintype G] (H : subgroup G) : set (subgroup G) :=
--   { J | subgroups_are_conj H J ∧ ∃ p : ℕ, is_sylow_subgroup J p }

noncomputable def index_of_subgroup [fintype G] (H : subgroup G) : ℕ :=
  card G / card H

lemma index_of_subgroup_def [fintype G] (H : subgroup G) : 
  index_of_subgroup H = card G / card H := rfl
 
lemma size_subgroup_gt_zero [fintype G] (H : subgroup G) : card H > 0 :=
begin

  sorry,
end

lemma index_of_subgroup_def2 [fintype G] (H : subgroup G) :
  index_of_subgroup H = card (quotient H) := 
begin
  rw index_of_subgroup_def, 
  -- lagranges theorem
  rw card_eq_card_quotient_mul_card_subgroup H,
  rw nat.mul_div_assoc _ (dvd_refl (card ↥H)),
  rw nat.div_self (size_subgroup_gt_zero H),
  simp,
end


--TODO: remove unfold here

-- this is my previous h₃ and h₄ combined
-- h₃ : ¬ p ∣ index_of_subgroup H,
-- h₄ : ¬ index_of_subgroup H ≡ 0 [MOD p]
lemma not_subgroup_index_conj_zero_wrt_p [fintype G] {H : subgroup G} {p m n : ℕ}
(hp : p.prime) (hG : card G = p ^ n * m) (hndiv: ¬ p ∣ m) (h : is_sylow_subgroup H hp hG hndiv) 
  : ¬ index_of_subgroup H ≡ 0 [MOD p] :=
begin
  intro hn,
  rw [nat.modeq.modeq_zero_iff, index_of_subgroup, hG] at hn,
  unfold is_sylow_subgroup at h,
  rw [h, mul_comm, nat.mul_div_cancel _ (pow_pos (pos_of_gt hp.left) n)] at hn,
  apply hndiv,
  exact hn,
end


example (p m n : ℕ) (h1: p > 0) (h2: n >= m): p ^ n / p ^ m = p ^ (n - m) :=
begin
  exact pow_div h2 h1,
end


-- to prove prime is greater than 0 : exact pos_of_gt hp.left

-- useful
-- use modeq.mod_modeq and transitivity to change between % notation and [MOD] notation




/-- Formulation of second sylow theorem -/
-- Alternative definition would be set_of_conjug_subgroups H = set_of_sylow_subgroups p
-- from kbuzzards group theory game
-- need to remove unfold of is_sylow_subgroup
theorem sylow_two [fintype G] {p n m : ℕ} [fintype G] (H : subgroup G) {p m n : ℕ} (hp : p.prime)
(hG : card G = p ^ n * m) (hndiv: ¬ p ∣ m) (H K : subgroup G) ( h₁ : is_sylow_subgroup H hp hG hndiv)
 (h₂ : is_sylow_subgroup K hp hG hndiv) : subgroups_are_conj H K :=
begin
  have h₃ : (index_of_subgroup K) ≡ (index_of_subgroup H) [MOD p], {
    repeat {rw index_of_subgroup},
    unfold is_sylow_subgroup at *,
    rw [hG, h₁, h₂],
  },
  have h₄ : (index_of_subgroup K) ≠ 0, {
    intro h,
    rw h at h₃,
    apply not_subgroup_index_conj_zero_wrt_p hp hG hndiv h₁,
    exact modeq.symm h₃,
  },
  have h₅ : ∀ x : G, conjugate_subgroup K x ≤ H, {
    sorry,
  },
  rw subgroups_are_conj,
  unfold subgroups_are_conj_by_x,


  -- want to show its equiv to h₄ ie K a normal subgroup of H
  -- and they have the same size => subgroups are equal


  -- let H' be the set of left cosets of H
      -- this is my aux_action
  -- let K act on H' by y(xH) = (yx)H, y ∈ K, (x is forming the coset from H to H')
  
  -- |K'| ≡ |H'| (mod p) -- i have this in my lemma
  -- |H'| = (G : H)  not div by p   -- I have this in my lemma

  -- so |K'| ≠ 0 -- index K ≠ 0 -- i have this as theorem h₄

  -- let xH ∈ K'
  -- then yxH = xH, ∀ y ∈ K     so x⁻¹yxH = H, ∀ y ∈ K -- this is my aux_lemma
  -- so x⁻¹Hx ≤ K -- this is theorem h₄
  -- since |H| = |K|, |x⁻¹Hx| = |K|, so x⁻¹Hx = K so are conjugate subgroups

  sorry,
end

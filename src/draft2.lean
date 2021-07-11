import group_theory.group_action
import group_theory.group_action.basic
import group_theory.quotient_group
import group_theory.order_of_element
import data.zmod.basic
import data.fintype.card
import data.list.rotate
import algebra.group.conj
import group_theory.sylow


open equiv fintype finset mul_action function nat sylow
open subgroup quotient_group
-- open_locale big_operators
universes u v w
variables {G : Type u} {α : Type v} {β : Type w} [group G]

local attribute [instance, priority 10] subtype.fintype set_fintype classical.prop_decidable

/-- Useful standard library functions
quotient H - set of all left cosets
conjugates, is_conj
p.prime - predicate

-/

-- concerned no mention of p.prime 
-- by KBuzzard
def is_sylow_subgroup [fintype G] (H : subgroup G) (p : ℕ) :=
  ∃ m n : ℕ, card G = p ^ n * m ∧ ¬ p ∣ m ∧ card H = p ^ n

namespace is_sylow_subgroup

variables [fintype G] {H : subgroup G} {p : ℕ} (h : is_sylow_subgroup H p)

noncomputable def m := classical.some h
noncomputable def n := classical.some (classical.some_spec h)

lemma card_G : card G = p ^ h.n * h.m := (classical.some_spec (classical.some_spec h)).1
lemma not_p_div_m : ¬ p ∣ h.m :=  (classical.some_spec (classical.some_spec h)).2.1
lemma card_H : card H = p ^ h.n := (classical.some_spec (classical.some_spec h)).2.2

end is_sylow_subgroup




-- def conjugate_subgroup (H : subgroup G) (g : G) : subgroup G :=
--  { carrier := { c | ∃ h ∈ H, c = g⁻¹ * h * g },
--   one_mem' := 
-- begin
--   use 1,
--   split,
--   exact one_mem H,
--   simp,  
-- end,
--   mul_mem' := 
-- begin
--   intros a b ha hb,
--   simp,
--   use g * a * b * g⁻¹,
--   split,
--   {
--     -- introduce a g * g⁻¹ between a * b or sim.
--     -- then replace with h and h' from ha hb
    
--     sorry,
--   },
--   rw [mul_assoc, mul_assoc, inv_mul_self g, mul_assoc, mul_one, ← mul_assoc],
--   simp,
-- end,
--   inv_mem' := 
-- begin
--   simp,
--   intros x y hy hx,
--   use (g * x * g⁻¹)⁻¹,
--   split,
--   {
--     rw [hx, mul_assoc, mul_assoc, mul_assoc, mul_inv_self, mul_one, ← mul_assoc, mul_inv_self, one_mul],
--     exact inv_mem H hy,
--   },
--   simp,
--   rw [mul_assoc, mul_assoc, mul_assoc, inv_mul_self, mul_one, ← mul_assoc, inv_mul_self],
--   simp,
-- end }

def subgroups_are_conj_by_x (H K : subgroup G) (g : G) :=
  { c | ∃ h ∈ H, c = g⁻¹ * h * g } = K
  -- conjugate_subgroup H x = K -- once I have all the proofs for this

def subgroups_are_conj (H K : subgroup G) := 
  ∃ g : G, subgroups_are_conj_by_x H K g

def set_of_sylow_subgroups (p : ℕ) [fintype G] : set (subgroup G) :=
  { H | is_sylow_subgroup H p }

def set_of_conjug_subgroups [fintype G] (H : subgroup G) : set (subgroup G) :=
  { J | subgroups_are_conj H J ∧ ∃ p : ℕ, is_sylow_subgroup J p }


-- this must exist properly somewhere in mathlib
-- TODO: find it and replace
noncomputable def index_of_subgroup [fintype G] (H : subgroup G) : ℕ :=
  card G / card H

lemma index_of_subgroup_def [fintype G] (H : subgroup G) : 
  index_of_subgroup H = card G / card H := rfl

-- proof of this by lagranges theorem 
-- lemma index_of_subgroup_def2 [fintype G] (H : subgroup G) :
--   index_of_subgroup H = card (quotient H) := sorry


-- def aux_action (K : subgroup G) (H : subgroup G) (k : G) {a : G} (h' : left_coset a H.carrier) 
--   := left_coset (k * a) H.carrier

-- need the lemma from the proof here as aux_lemma

open is_sylow_subgroup

/-- Formulation of second sylow theorem -/
-- Alternative definition would be set_of_conjug_subgroups H = set_of_sylow_subgroups p
-- from kbuzzards group theory game
-- hG is in is_sylow_subgroup_p - attempt to remove?


-- this is my previous h₃ and h₄ combined
-- h₃ : ¬ p ∣ index_of_subgroup H,
-- h₄ : ¬ index_of_subgroup H ≡ 0 [MOD p]
lemma not_subgroup_index_conj_zero_wrt_p [fintype G] {H : subgroup G} {p : ℕ} (h : is_sylow_subgroup H p) 
  (hp : p.prime) : ¬ index_of_subgroup H ≡ 0 [MOD p] :=
begin
  intro hn,
  rw [nat.modeq.modeq_zero_iff, index_of_subgroup, card_G h, card_H h, mul_comm] at hn,
  rw nat.mul_div_cancel _ (pow_pos (pos_of_gt hp.left) h.n) at hn,
  apply not_p_div_m h,
  exact hn,
end

theorem sylow_two [fintype G] {p m n: ℕ} (hp : p.prime) (hG : card G = p ^ n * m)
 (H K : subgroup G) ( h₁ : is_sylow_subgroup H p )
  (h₂ : is_sylow_subgroup K p) : 
    subgroups_are_conj H K :=
begin
  have h₅ : (index_of_subgroup K) ≡ (index_of_subgroup H) [MOD p], {
    repeat {rw index_of_subgroup},
    rw [card_G h₁, card_H h₁, card_H h₂, mul_comm],
    rw nat.mul_div_cancel _ (pow_pos (pos_of_gt hp.left) h₁.n),
    refine modeq.symm _,
    sorry,
  },
  have h₆ : (index_of_subgroup K) ≠ 0, {
    intro h,
    rw h at h₅,
    apply not_subgroup_index_conj_zero_wrt_p h₁ hp,
    exact modeq.symm h₅,
  },

  -- want to rewrite this to say expression is a subgroup of H
  -- atm I think it says expression is a subset of H
 
  have h₇ : ∀ x : G, (right_coset (left_coset x⁻¹ K) x) ≤ H, {
    sorry,
  },
  rw subgroups_are_conj,
  unfold subgroups_are_conj_by_x,


  -- want to show its equiv to h₆ ie K a normal subgroup of H
  -- and they have the same size => subgroups are equal


  -- let H' be the set of left cosets of H
      -- this is my aux_action
  -- let K act on H' by y(xH) = (yx)H, y ∈ K, (x is forming the coset from H to H')
  
  -- |K'| ≡ |H'| (mod p) -- i have this as theorem h₅
  -- |H'| = (G : H)  not div by p   -- I have this as theorem h₄

  -- so |K'| ≠ 0 -- index K ≠ 0 -- i have this as theorem h₆

  -- let xH ∈ K'
  -- then yxH = xH, ∀ y ∈ K     so x⁻¹yxH = H, ∀ y ∈ K -- this is my aux_lemma
  -- so x⁻¹Hx ≤ K -- this is theorem h₆
  -- since |H| = |K|, |x⁻¹Hx| = |K|, so x⁻¹Hx = K so are conjugate subgroups

  sorry,
end


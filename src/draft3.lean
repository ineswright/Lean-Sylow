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


def is_sylow_subgroup [fintype G] (H : subgroup G) {p m n : ℕ} (hp : p.prime)
(hG : card G = p ^ n * m) (hndiv: ¬ p ∣ m) :=
  card H = p ^ n

namespace is_sylow_subgroup
variables [fintype G] {H : subgroup G} {p m n : ℕ} {hp : p.prime}
{hG : card G = p ^ n * m} {hndiv: ¬ p ∣ m} (h : is_sylow_subgroup H hp hG hndiv)

end is_sylow_subgroup

lemma is_sylow_subgroup_def [fintype G] (H : subgroup G) {p m n : ℕ} (hp : p.prime)
(hG : card G = p ^ n * m) (hndiv: ¬ p ∣ m) : is_sylow_subgroup H hp hG hndiv ↔ (card H = p ^ n)
:= iff.rfl

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


def subgroups_conj_by_x (H K : subgroup G) (x : G) :=
  conjugate_subgroup H x = K

lemma subgroups_conj_by_x_def (H K : subgroup G) (x : G) : 
  conjugate_subgroup H x = K ↔ subgroups_conj_by_x H K x := iff.rfl

def subgroups_are_conj (H K : subgroup G) := 
  ∃ g : G, subgroups_conj_by_x H K g

def set_of_sylow_subgroups [fintype G] {p m n : ℕ} (hp : p.prime) (hG : card G = p ^ n * m) 
  (hndiv: ¬ p ∣ m) : set (subgroup G) :=
  { H | is_sylow_subgroup H hp hG hndiv }

-- def set_of_conjug_subgroups [fintype G] (H : subgroup G) : set (subgroup G) :=
--   { J | subgroups_are_conj H J ∧ ∃ p : ℕ, is_sylow_subgroup J p }

noncomputable def index_of_subgroup [fintype G] (H : subgroup G) : ℕ :=
  card G / card H

lemma index_of_subgroup_def [fintype G] (H : subgroup G) : 
  index_of_subgroup H = card G / card H := rfl
 
lemma card_subgroup_pos [fintype G] (H : subgroup G) : 0 < card H :=
card_pos_iff.2 $ nonempty.intro ⟨1, H.one_mem⟩

-- lagranges theorem
lemma index_of_subgroup_def2 [fintype G] (H : subgroup G) :
  index_of_subgroup H = card (quotient H) := 
begin
  rw [index_of_subgroup_def, card_eq_card_quotient_mul_card_subgroup H],
  rw [nat.mul_div_assoc _ (dvd_refl (card ↥H)), nat.div_self (card_subgroup_pos H)],
  simp,
end

-- this is my previous h₃ and h₄ combined
-- h₃ : ¬ p ∣ index_of_subgroup H,
-- h₄ : ¬ index_of_subgroup H ≡ 0 [MOD p]
lemma not_subgroup_index_conj_zero_wrt_p [fintype G] {H : subgroup G} {p m n : ℕ}
(hp : p.prime) (hG : card G = p ^ n * m) (hndiv: ¬ p ∣ m) (h : is_sylow_subgroup H hp hG hndiv) 
  : ¬ index_of_subgroup H ≡ 0 [MOD p] :=
begin
  intro hn,
  rw [nat.modeq.modeq_zero_iff, index_of_subgroup, hG] at hn,
  rw is_sylow_subgroup_def at h,
  rw [h, mul_comm, nat.mul_div_cancel _ (pow_pos (pos_of_gt hp.left) n)] at hn,
  apply hndiv,
  exact hn,
end

example (a b c d : ℕ) (h1: a ≡ b [MOD d]) (h2: b ≡ c [MOD d]) : a ≡ c [MOD d] :=
begin
  exact modeq.trans h1 h2,
end


#check card_modeq_card_fixed_points

-- useful
-- use modeq.mod_modeq and transitivity to change between % notation and [MOD] notation
-- pow_div := p ^ n / p ^ m = p ^ (n - m)
-- to prove prime is greater than 0 : exact pos_of_gt hp.left

/-- Formulation of second sylow theorem -/
-- Alternative definition would be set_of_conjug_subgroups H = set_of_sylow_subgroups p
-- from kbuzzards group theory game

-- in mul_action A B, A is the group and B is the set where B -> f(B)
-- i have K acting on quotient H

theorem sylow_two [fintype G] {p n m : ℕ} [fintype G] (H K : subgroup G) {p m n : ℕ} 
(hp : p.prime) (hG : card G = p ^ n * m) (hndiv: ¬ p ∣ m) [mul_action K (quotient H)]
( h₁ : is_sylow_subgroup H hp hG hndiv) (h₂ : is_sylow_subgroup K hp hG hndiv)
 : subgroups_are_conj H K :=
begin
  haveI : fact (p.prime) := ⟨ hp ⟩ ,
  have h₃ : ¬ index_of_subgroup H ≡ 0 [MOD p], {
    intro hn,
    rw [nat.modeq.modeq_zero_iff, index_of_subgroup, hG] at hn,
    rw is_sylow_subgroup_def at h₁,
    rw [h₁, mul_comm, nat.mul_div_cancel _ (pow_pos (pos_of_gt hp.left) n)] at hn,
    apply hndiv,
    exact hn,
  },
  have h₄ : index_of_subgroup H ≡ card (fixed_points K (quotient H)) [MOD p], {
    rw is_sylow_subgroup_def at h₂,
    rw index_of_subgroup_def2,
    exact card_modeq_card_fixed_points p h₂,
  },
  -- this should probably be 0 < 
  -- then use trichotomy and this proof
  have h₅ : 0 ≠ card (fixed_points K (quotient H)), {
    intro hn,
    apply not_subgroup_index_conj_zero_wrt_p hp hG hndiv h₁,
    rw hn,
    exact h₄,
  },
  -- have x⁻¹Hx ≤ K and |H| = |K|
  -- so |x⁻¹Hx| (= |H|) = |K|
  -- and x⁻¹Hx ≤ K so x⁻¹Hx = K
  -- is def of H and K being conj




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

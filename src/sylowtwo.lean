/- Need to check how many of these I'm actually using -/
-- import group_theory.group_action
-- import group_theory.quotient_group
-- import group_theory.order_of_element
-- import data.zmod.basic
-- import data.fintype.card
-- import data.list.rotate
-- does this import all of group_theory.sylows imports?
import group_theory.sylow
import tactic
-- import algebra.group.conj

open equiv fintype finset mul_action function nat sylow
open subgroup quotient_group
universe u
variables {G : Type u} [group G]

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
  exact ⟨1, one_mem L, by simp⟩,
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
  refine ⟨(g * x * g⁻¹)⁻¹, _, by group⟩,
  rw [hx, mul_assoc, mul_assoc, mul_assoc, mul_inv_self, mul_one, ← mul_assoc, mul_inv_self, one_mul],
  exact inv_mem L hy,
end }

lemma conjugate_subgroup_def (L : subgroup G) (x g : G) : 
  x ∈ conjugate_subgroup L g ↔ x ∈  { c | ∃ h ∈ L, c = g⁻¹ * h * g } := iff.rfl

def subgroups_conj_by_x (L K : subgroup G) (x : G) :=
  conjugate_subgroup L x = K

def subgroups_are_conj (L K : subgroup G) := 
  ∃ g : G, subgroups_conj_by_x L K g

-- not actually using rn- maybe delete
-- def set_of_sylow_subgroups [fintype G] {p m n : ℕ} (hp : p.prime) (hG : card G = p ^ n * m) 
--   (hndiv: ¬ p ∣ m) : set (subgroup G) :=
--   { L | is_sylow_subgroup L hp hG hndiv }

-- def set_of_conjug_subgroups [fintype G] (L : subgroup G) : set (subgroup G) :=
--   { J | subgroups_are_conj L J ∧ ∃ p : ℕ, is_sylow_subgroup J p }

noncomputable def index_of_subgroup [fintype G] (L : subgroup G) : ℕ :=
  card G / card L

lemma index_of_subgroup_def [fintype G] (L : subgroup G) : 
  index_of_subgroup L = card G / card L := rfl
 
lemma card_subgroup_pos [fintype G] (L : subgroup G) : 0 < card L :=
card_pos_iff.2 $ nonempty.intro ⟨1, L.one_mem⟩

-- lagranges theorem
lemma index_of_subgroup_def' [fintype G] (L : subgroup G) :
  index_of_subgroup L = card (quotient L) := 
begin
  rw [index_of_subgroup_def, card_eq_card_quotient_mul_card_subgroup L],
  rw [nat.mul_div_assoc _ (dvd_refl (card ↥L)), nat.div_self (card_subgroup_pos L)],
  simp,
end 



-- TODO!!
def subgroup_to_conjugate (x : G) (L : subgroup G) -- (K : ↥L) 
: ↥(conjugate_subgroup L x) := sorry

def conjugate_to_subgroup {L : subgroup G} {x : G} (y : (conjugate_subgroup L x)) 
: ↥L := sorry

def subgroup_bijects_conjugate (L : subgroup G) (x : G) : 
conjugate_subgroup L x ≃ L := sorry
-- { to_fun := conjugate_to_subgroup,
--   inv_fun := _,
--   left_inv := _,
--   right_inv := _ }




lemma sylow_subgroup_index_equal_m [fintype G] {L : subgroup G} {p m n : ℕ}
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
  rw sylow_subgroup_index_equal_m hp hG hndiv h,
  intro hn,
  apply hndiv,
  exact modeq.modeq_zero_iff.mp hn,
end


theorem sylow_two [fintype G] {p n m : ℕ} (L K : subgroup G) 
(hp : p.prime) (hG : card G = p ^ n * m) (hndiv: ¬ p ∣ m)
( h₁ : is_sylow_subgroup L hp hG hndiv) (h₂ : is_sylow_subgroup K hp hG hndiv)
: subgroups_are_conj K L :=
begin
  haveI : fact (p.prime) := ⟨ hp ⟩,
  have h₄ : index_of_subgroup L ≡ card (fixed_points K (quotient L)) [MOD p], {
    rw is_sylow_subgroup_def at h₂,
    rw index_of_subgroup_def',
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
    let y := quotient.out' fp,
    use y,
    intros c hc,
    rw conjugate_subgroup_def at hc,
    rcases hc with ⟨x, hx, rfl⟩,


    -- fp : yL
    -- y : G
    -- x * yL = yL
    -- y⁻¹ * x * yL = y⁻¹ * yL = L

  -- let xL ∈ fixed points of action
  -- then yxL = xL, ∀ y ∈ K     so x⁻¹yxL = L, ∀ y ∈ K
  -- so x⁻¹Lx ≤ K
    sorry,
  },
  have h₇ : ∀ x : G, card (conjugate_subgroup K x) = card L, {
    rw is_sylow_subgroup_def at h₁ h₂,
    intro x,
    rw [h₁, h₂.symm],
    apply fintype.card_congr,
    exact subgroup_bijects_conjugate K x,
  },
  have h₇' : ∀ x : G, card L ≤ card (conjugate_subgroup K x), {
    intro x,
    exact (h₇ x).ge,
  },
  have h₈ : ∃ x : G, ( (conjugate_subgroup K x) = L), {
    apply exists.elim h₆,
    intros x hx,
    use x,
    -- is the problem because i have ≤ and not ⊆ ?
    -- exact set.eq_of_subset_of_card_le hx (h₇ x).ge,
    sorry,
  },
  exact h₈,
end

-- example {A : Type u} [group A] [fintype A] (H K : subgroup A) (h1: H ⊆ K) 
-- (h2 : card K ≤ card H) : H = K :=
-- begin
--   exact eq_of_subset_of_card_le h1 h2,
--   sorry,
-- end

example ( a b : ℕ) (h : a = b) : b ≤ a := begin
  exact eq.ge h,
end
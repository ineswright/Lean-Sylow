import group_theory.group_action
import group_theory.quotient_group
import data.zmod.basic
import data.fintype.card
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

-- TODO: think about using conjugation function
-- def conjugate (x y : G) := x⁻¹ * y * x

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

def subgroups_are_conj (L K : subgroup G) := 
  ∃ g : G, conjugate_subgroup L g  = K

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

lemma quotient_iff_set {x y : G} {L : subgroup G}
: @quotient_group.mk _ _ L x = quotient_group.mk y ↔ left_coset x L = left_coset y L := 
begin
  sorry,
end


-- think about replacing λ with a conjugation function
-- will almost definitely need to do this for mathlib anyway
def subgroup_bijects_conjugate (L : subgroup G) (x : G) : 
conjugate_subgroup L x ≃ L :=
{ to_fun := (λ y : conjugate_subgroup L x, ⟨x * y * x⁻¹, 
begin
  rcases y with ⟨_, z, hz, rfl⟩,
  rw [subtype.coe_mk, mul_assoc, mul_assoc, mul_inv_self, mul_one, ← mul_assoc, mul_inv_self, one_mul],
  exact hz,
end⟩) ,
  inv_fun := (λ y : L, ⟨x⁻¹ * y * x, ⟨y, set_like.coe_mem y, rfl⟩⟩),
  left_inv := 
  begin
    rintro ⟨y, hy⟩,
    simp only [subtype.mk_eq_mk, subtype.coe_mk],
    group,
  end,
  right_inv := 
  begin
    rintro ⟨y, hy⟩,
    simp only [subtype.mk_eq_mk, subtype.coe_mk],
    group,
  end }


lemma sylow_subgroup_index [fintype G] {L : subgroup G} {p m n : ℕ}
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
  rw sylow_subgroup_index hp hG hndiv h,
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
  have h₆ : ∃ x : G, (conjugate_subgroup K x : set G) ⊆ L, {
    rw card_pos_iff at h₅,
    rcases h₅ with ⟨fp, hfp⟩,
    rw mul_action.mem_fixed_points at hfp,
    let x := quotient.out' fp,
    use x,
    rintro _ ⟨y, hy, rfl⟩,
    have h1 : y • fp = quotient_group.mk (y * x), {
      rw ← quotient.out_eq' fp,
      exact quotient.smul_mk L y x,
    },
    have h2 : @quotient_group.mk _ _ L (x⁻¹ * y * x) = quotient_group.mk 1, {
      rw [mul_assoc, ← quotient.smul_mk L x⁻¹ (y * x)],
      rw [← smul_left_cancel_iff x, smul_smul x x⁻¹ _, mul_inv_self, quotient.smul_mk, one_mul],
      rw [quotient.smul_mk, mul_one, ← h1],
      convert hfp ⟨y, hy⟩,
      exact quotient.out_eq' fp,
    },
    rw [quotient_iff_set, one_left_coset] at h2,
    rw ← h2,
    unfold left_coset,
    simp only [mul_inv_rev, set.mem_preimage, set.image_mul_left, set_like.mem_coe, inv_inv],
    rw [mul_assoc, mul_assoc, mul_assoc, ← mul_assoc x x⁻¹ (y * x)],
    rw [mul_inv_self, one_mul, ← mul_assoc, ← mul_assoc],
    simp [mul_left_inv, inv_mul_cancel_right, one_mem L],
  },
  have h₇ : ∀ x : G, card (conjugate_subgroup K x) = card L, {
    rw is_sylow_subgroup_def at h₁ h₂,
    intro x,
    rw [h₁, h₂.symm],
    apply fintype.card_congr,
    exact subgroup_bijects_conjugate K x,
  },
  apply exists.elim h₆,
  intros x hx,
  use x,
  rw set_like.ext'_iff,
  exact set.eq_of_subset_of_card_le hx (h₇ x).ge,
end

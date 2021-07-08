-- Time to write some actual code I guess - A COPY OF SYLOW.LEAN

/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import group_theory.group_action
import group_theory.group_action.basic
import group_theory.quotient_group
import group_theory.order_of_element
import data.zmod.basic
import data.fintype.card
import data.list.rotate
import algebra.group.conj

/-!
# Sylow theorems

The Sylow theorems are the following results for every finite group `G` and every prime number `p`.

* There exists a Sylow `p`-subgroup of `G`.
* All Sylow `p`-subgroups of `G` are conjugate to each other.
* Let `nₚ` be the number of Sylow `p`-subgroups of `G`, then `nₚ` divides the index of the Sylow
  `p`-subgroup, `nₚ ≡ 1 [MOD p]`, and `nₚ` is equal to the index of the normalizer of the Sylow
  `p`-subgroup in `G`.

In this file, currently only the first of these results is proven.

## Main statements

* `exists_prime_order_of_dvd_card`: For every prime `p` dividing the order of `G` there exists an
  element of order `p` in `G`. This is known as Cauchy`s theorem.
* `exists_subgroup_card_pow_prime`: A generalisation of the first of the Sylow theorems: For every
  prime power `pⁿ` dividing `G`, there exists a subgroup of `G` of order `pⁿ`.

## TODO

* Prove the second and third of the Sylow theorems.
* Sylow theorems for infinite groups
-/

open equiv fintype finset mul_action function
open equiv.perm subgroup list quotient_group
open_locale big_operators
universes u v w
variables {G : Type u} {α : Type v} {β : Type w} [group G]

local attribute [instance, priority 10] subtype.fintype set_fintype classical.prop_decidable

namespace mul_action
variables [mul_action G α]

lemma mem_fixed_points_iff_card_orbit_eq_one {a : α}
  [fintype (orbit G a)] : a ∈ fixed_points G α ↔ card (orbit G a) = 1 :=
begin
  rw [fintype.card_eq_one_iff, mem_fixed_points],
  split,
  { exact λ h, ⟨⟨a, mem_orbit_self _⟩, λ ⟨b, ⟨x, hx⟩⟩, subtype.eq $ by simp [h x, hx.symm]⟩ },
  { assume h x,
    rcases h with ⟨⟨z, hz⟩, hz₁⟩,
    exact calc x • a = z : subtype.mk.inj (hz₁ ⟨x • a, mem_orbit _ _⟩)
      ... = a : (subtype.mk.inj (hz₁ ⟨a, mem_orbit_self _⟩)).symm }
end

lemma card_modeq_card_fixed_points [fintype α] [fintype G] [fintype (fixed_points G α)]
  (p : ℕ) {n : ℕ} [hp : fact p.prime] (h : card G = p ^ n) :
  card α ≡ card (fixed_points G α) [MOD p] :=
calc card α = card (Σ y : quotient (orbit_rel G α), {x // quotient.mk' x = y}) :
  card_congr (sigma_preimage_equiv (@quotient.mk' _ (orbit_rel G α))).symm
... = ∑ a : quotient (orbit_rel G α), card {x // quotient.mk' x = a} : card_sigma _
... ≡ ∑ a : fixed_points G α, 1 [MOD p] :
begin
  rw [← zmod.eq_iff_modeq_nat p, sum_nat_cast, sum_nat_cast],
  refine eq.symm (sum_bij_ne_zero (λ a _ _, quotient.mk' a.1)
    (λ _ _ _, mem_univ _)
    (λ a₁ a₂ _ _ _ _ h,
      subtype.eq ((mem_fixed_points' α).1 a₂.2 a₁.1 (quotient.exact' h)))
      (λ b, _)
      (λ a ha _, by rw [← mem_fixed_points_iff_card_orbit_eq_one.1 a.2];
        simp only [quotient.eq']; congr)),
  { refine quotient.induction_on' b (λ b _ hb, _),
    have : card (orbit G b) ∣ p ^ n,
    { rw [← h, fintype.card_congr (orbit_equiv_quotient_stabilizer G b)],
      exact card_quotient_dvd_card _ },
    rcases (nat.dvd_prime_pow hp.1).1 this with ⟨k, _, hk⟩,
    have hb' :¬ p ^ 1 ∣ p ^ k,
    { rw [pow_one, ← hk, ← nat.modeq.modeq_zero_iff, ← zmod.eq_iff_modeq_nat,
        nat.cast_zero, ← ne.def],
      exact eq.mpr (by simp only [quotient.eq']; congr) hb },
    have : k = 0 := nat.le_zero_iff.1 (nat.le_of_lt_succ (lt_of_not_ge (mt (pow_dvd_pow p) hb'))),
    refine ⟨⟨b, mem_fixed_points_iff_card_orbit_eq_one.2 $ by rw [hk, this, pow_zero]⟩,
      mem_univ _, _, rfl⟩,
    rw [nat.cast_one], exact one_ne_zero }
end
... = _ : by simp; refl

end mul_action

lemma quotient_group.card_preimage_mk [fintype G] (s : subgroup G)
  (t : set (quotient s)) : fintype.card (quotient_group.mk ⁻¹' t) =
  fintype.card s * fintype.card t :=
by rw [← fintype.card_prod, fintype.card_congr
  (preimage_mk_equiv_subgroup_times_set _ _)]

namespace sylow

/-- Given a vector `v` of length `n`, make a vector of length `n+1` whose product is `1`,
by consing the the inverse of the product of `v`. -/
def mk_vector_prod_eq_one (n : ℕ) (v : vector G n) : vector G (n+1) :=
v.to_list.prod⁻¹ ::ᵥ v

lemma mk_vector_prod_eq_one_injective (n : ℕ) : injective (@mk_vector_prod_eq_one G _ n) :=
λ ⟨v, _⟩ ⟨w, _⟩ h, subtype.eq (show v = w, by injection h with h; injection h)

/-- The type of vectors with terms from `G`, length `n`, and product equal to `1:G`. -/
def vectors_prod_eq_one (G : Type*) [group G] (n : ℕ) : set (vector G n) :=
{v | v.to_list.prod = 1}

lemma mem_vectors_prod_eq_one {n : ℕ} (v : vector G n) :
  v ∈ vectors_prod_eq_one G n ↔ v.to_list.prod = 1 := iff.rfl

lemma mem_vectors_prod_eq_one_iff {n : ℕ} (v : vector G (n + 1)) :
  v ∈ vectors_prod_eq_one G (n + 1) ↔ v ∈ set.range (@mk_vector_prod_eq_one G _ n) :=
⟨λ (h : v.to_list.prod = 1), ⟨v.tail,
  begin
    unfold mk_vector_prod_eq_one,
    conv {to_rhs, rw ← vector.cons_head_tail v},
    suffices : (v.tail.to_list.prod)⁻¹ = v.head,
    { rw this },
    rw [← mul_left_inj v.tail.to_list.prod, inv_mul_self, ← list.prod_cons,
      ← vector.to_list_cons, vector.cons_head_tail, h]
  end⟩,
  λ ⟨w, hw⟩, by rw [mem_vectors_prod_eq_one, ← hw, mk_vector_prod_eq_one,
    vector.to_list_cons, list.prod_cons, inv_mul_self]⟩

/-- The rotation action of `zmod n` (viewed as multiplicative group) on
`vectors_prod_eq_one G n`, where `G` is a multiplicative group. -/
def rotate_vectors_prod_eq_one (G : Type*) [group G] (n : ℕ)
  (m : multiplicative (zmod n)) (v : vectors_prod_eq_one G n) : vectors_prod_eq_one G n :=
⟨⟨v.1.to_list.rotate m.val, by simp⟩, prod_rotate_eq_one_of_prod_eq_one v.2 _⟩

instance rotate_vectors_prod_eq_one.mul_action (n : ℕ) [fact (0 < n)] :
  mul_action (multiplicative (zmod n)) (vectors_prod_eq_one G n) :=
{ smul := (rotate_vectors_prod_eq_one G n),
  one_smul :=
  begin
    intro v, apply subtype.eq, apply vector.eq _ _,
    show rotate _ (0 : zmod n).val = _, rw zmod.val_zero,
    exact rotate_zero v.1.to_list
  end,
  mul_smul := λ a b ⟨⟨v, hv₁⟩, hv₂⟩, subtype.eq $ vector.eq _ _ $
    show v.rotate ((a + b : zmod n).val) = list.rotate (list.rotate v (b.val)) (a.val),
    by rw [zmod.val_add, rotate_rotate, ← rotate_mod _ (b.val + a.val), add_comm, hv₁] }

lemma one_mem_vectors_prod_eq_one (n : ℕ) : vector.repeat (1 : G) n ∈ vectors_prod_eq_one G n :=
by simp [vector.repeat, vectors_prod_eq_one]

lemma one_mem_fixed_points_rotate (n : ℕ) [fact (0 < n)] :
  (⟨vector.repeat (1 : G) n, one_mem_vectors_prod_eq_one n⟩ : vectors_prod_eq_one G n) ∈
  fixed_points (multiplicative (zmod n)) (vectors_prod_eq_one G n) :=
λ m, subtype.eq $ vector.eq _ _ $
rotate_eq_self_iff_eq_repeat.2 ⟨(1 : G),
  show list.repeat (1 : G) n = list.repeat 1 (list.repeat (1 : G) n).length, by simp⟩ _

/-- Cauchy's theorem -/
lemma exists_prime_order_of_dvd_card [fintype G] (p : ℕ) [hp : fact p.prime]
  (hdvd : p ∣ card G) : ∃ x : G, order_of x = p :=
let n : ℕ+ := ⟨p - 1, nat.sub_pos_of_lt hp.1.one_lt⟩ in
have hn : p = n + 1 := nat.succ_sub hp.1.pos,
have hcard : card (vectors_prod_eq_one G (n + 1)) = card G ^ (n : ℕ),
  by rw [set.ext mem_vectors_prod_eq_one_iff,
    set.card_range_of_injective (mk_vector_prod_eq_one_injective _), card_vector],
have hzmod : fintype.card (multiplicative (zmod p)) = p ^ 1,
  by { rw pow_one p, exact zmod.card p },
have hmodeq : _ = _ := @mul_action.card_modeq_card_fixed_points
  (multiplicative (zmod p)) (vectors_prod_eq_one G p) _ _ _ _ _ _ 1 hp hzmod,
have hdvdcard : p ∣ fintype.card (vectors_prod_eq_one G (n + 1)) :=
  calc p ∣ card G ^ 1 : by rwa pow_one
  ... ∣ card G ^ (n : ℕ) : pow_dvd_pow _ n.2
  ... = card (vectors_prod_eq_one G (n + 1)) : hcard.symm,
have hdvdcard₂ : p ∣ card (fixed_points (multiplicative (zmod p)) (vectors_prod_eq_one G p)),
  by { rw nat.dvd_iff_mod_eq_zero at hdvdcard ⊢, rwa [← hn, hmodeq] at hdvdcard },
have hcard_pos : 0 < card (fixed_points (multiplicative (zmod p)) (vectors_prod_eq_one G p)) :=
  fintype.card_pos_iff.2 ⟨⟨⟨vector.repeat 1 p, one_mem_vectors_prod_eq_one _⟩,
    one_mem_fixed_points_rotate _⟩⟩,
have hlt : 1 < card (fixed_points (multiplicative (zmod p)) (vectors_prod_eq_one G p)) :=
  calc (1 : ℕ) < p : hp.1.one_lt
  ... ≤ _ : nat.le_of_dvd hcard_pos hdvdcard₂,
let ⟨⟨⟨⟨x, hx₁⟩, hx₂⟩, hx₃⟩, hx₄⟩ := fintype.exists_ne_of_one_lt_card hlt
  ⟨_, one_mem_fixed_points_rotate p⟩ in
have hx : x ≠ list.repeat (1 : G) p, from λ h, by simpa [h, vector.repeat] using hx₄,
have ∃ a, x = list.repeat a x.length := by exactI rotate_eq_self_iff_eq_repeat.1 (λ n,
  have list.rotate x (n : zmod p).val = x :=
    subtype.mk.inj (subtype.mk.inj (hx₃ (n : zmod p))),
  by rwa [zmod.val_nat_cast, ← hx₁, rotate_mod] at this),
let ⟨a, ha⟩ := this in
⟨a, have hx1 : x.prod = 1 := hx₂,
  have ha1: a ≠ 1, from λ h, hx (ha.symm ▸ h ▸ hx₁ ▸ rfl),
  have a ^ p = 1, by rwa [ha, list.prod_repeat, hx₁] at hx1,
  (hp.1.2 _ (order_of_dvd_of_pow_eq_one this)).resolve_left
    (λ h, ha1 (order_of_eq_one_iff.1 h))⟩

open subgroup submonoid is_group_hom mul_action

lemma mem_fixed_points_mul_left_cosets_iff_mem_normalizer {H : subgroup G}
  [fintype ((H : set G) : Type u)] {x : G} :
  (x : quotient H) ∈ fixed_points H (quotient H) ↔ x ∈ normalizer H :=
⟨λ hx, have ha : ∀ {y : quotient H}, y ∈ orbit H (x : quotient H) → y = x,
  from λ _, ((mem_fixed_points' _).1 hx _),
  (inv_mem_iff _).1 (@mem_normalizer_fintype _ _ _ _inst_2 _ (λ n (hn : n ∈ H),
    have (n⁻¹ * x)⁻¹ * x ∈ H := quotient_group.eq.1 (ha (mem_orbit _ ⟨n⁻¹, H.inv_mem hn⟩)),
    show _ ∈ H, by {rw [mul_inv_rev, inv_inv] at this, convert this, rw inv_inv}
    )),
λ (hx : ∀ (n : G), n ∈ H ↔ x * n * x⁻¹ ∈ H),
(mem_fixed_points' _).2 $ λ y, quotient.induction_on' y $ λ y hy, quotient_group.eq.2
  (let ⟨⟨b, hb₁⟩, hb₂⟩ := hy in
  have hb₂ : (b * x)⁻¹ * y ∈ H := quotient_group.eq.1 hb₂,
  (inv_mem_iff H).1 $ (hx _).2 $ (mul_mem_cancel_left H (H.inv_mem hb₁)).1
  $ by rw hx at hb₂;
    simpa [mul_inv_rev, mul_assoc] using hb₂)⟩

def fixed_points_mul_left_cosets_equiv_quotient (H : subgroup G) [fintype (H : set G)] :
  mul_action.fixed_points H (quotient H) ≃
  quotient (subgroup.comap ((normalizer H).subtype : normalizer H →* G) H) :=
@subtype_quotient_equiv_quotient_subtype G (normalizer H : set G) (id _) (id _) (fixed_points _ _)
  (λ a, (@mem_fixed_points_mul_left_cosets_iff_mem_normalizer _ _ _ _inst_2 _).symm)
  (by intros; refl)

/-- The first of the Sylow theorems. -/
theorem exists_subgroup_card_pow_prime [fintype G] (p : ℕ) : ∀ {n : ℕ} [hp : fact p.prime]
  (hdvd : p ^ n ∣ card G), ∃ H : subgroup G, fintype.card H = p ^ n
| 0 := λ _ _, ⟨(⊥ : subgroup G), by convert card_bot⟩
| (n+1) := λ hp hdvd,
let ⟨H, hH2⟩ := @exists_subgroup_card_pow_prime _ hp
  (dvd.trans (pow_dvd_pow _ (nat.le_succ _)) hdvd) in
let ⟨s, hs⟩ := exists_eq_mul_left_of_dvd hdvd in
have hcard : card (quotient H) = s * p :=
  (nat.mul_left_inj (show card H > 0, from fintype.card_pos_iff.2
      ⟨⟨1, H.one_mem⟩⟩)).1
    (by rwa [← card_eq_card_quotient_mul_card_subgroup H, hH2, hs,
      pow_succ', mul_assoc, mul_comm p]),
have hm : s * p % p =
  card (quotient (subgroup.comap ((normalizer H).subtype : normalizer H →* G) H)) % p :=
  card_congr (fixed_points_mul_left_cosets_equiv_quotient H) ▸ hcard ▸
    @card_modeq_card_fixed_points _ _ _ _ _ _ _ p _ hp hH2,
have hm' : p ∣ card (quotient (subgroup.comap ((normalizer H).subtype : normalizer H →* G) H)) :=
  nat.dvd_of_mod_eq_zero
    (by rwa [nat.mod_eq_zero_of_dvd (dvd_mul_left _ _), eq_comm] at hm),
let ⟨x, hx⟩ := @exists_prime_order_of_dvd_card _ (quotient_group.quotient.group _) _ _ hp hm' in
have hequiv : H ≃ (subgroup.comap ((normalizer H).subtype : normalizer H →* G) H) :=
  ⟨λ a, ⟨⟨a.1, le_normalizer a.2⟩, a.2⟩, λ a, ⟨a.1.1, a.2⟩,
    λ ⟨_, _⟩, rfl, λ ⟨⟨_, _⟩, _⟩, rfl⟩,
-- begin proof of ∃ H : subgroup G, fintype.card H = p ^ n
⟨subgroup.map ((normalizer H).subtype) (subgroup.comap
  (quotient_group.mk' (comap H.normalizer.subtype H)) (gpowers x)),
begin
  show card ↥(map H.normalizer.subtype
    (comap (mk' (comap H.normalizer.subtype H)) (subgroup.gpowers x))) = p ^ (n + 1),
  suffices : card ↥(subtype.val '' ((subgroup.comap (mk' (comap H.normalizer.subtype H))
    (gpowers x)) : set (↥(H.normalizer)))) = p^(n+1),
  { convert this using 2 },
  rw [set.card_image_of_injective
        (subgroup.comap (mk' (comap H.normalizer.subtype H)) (gpowers x) : set (H.normalizer))
        subtype.val_injective,
      pow_succ', ← hH2, fintype.card_congr hequiv, ← hx, order_eq_card_gpowers,
      ← fintype.card_prod],
  exact @fintype.card_congr _ _ (id _) (id _) (preimage_mk_equiv_subgroup_times_set _ _)
end⟩


-- All Sylow `p`-subgroups of `G` are conjugate to each other.

/- A, B : sylow p-subgroups => ord G = pᵃm, p does not divide m, ord A = ord B = pᵃ 

required inputs: G, p,  maybe a, m but i think compute them from G and p
required assumptions (need input proofs) : p prime, ordG = pᵃm, p ¬∣ m, (ie a is maximal)
    or construct a and m from card G and p then need only p | ordG

-- A conjugacy class of G is an orbit under the conjugation action of G.
-/

-- i don't think i can use is_conj to check if A and B are conjugate
-- surely I need conjugation between subgroups- how?
-- but also struggling to use the orbit definition

def subgroups_are_conj_by_x (H K : subgroup G) (g : G) :=
{ c | ∃ h ∈ H, c = g⁻¹ * h * g } = K

-- FROM KEVIN BUZZARDS GROUP THEORY GAME
def subgroups_are_conj (H K : subgroup G) := 
  ∃ g : G, subgroups_are_conj_by_x H K g

-- adapted

def is_sylow_subgroup_p [fintype G] (H : subgroup G) (p : ℕ) :=
    ∃ m n : ℕ, card H = p ^ n ∧ p.prime ∧ ¬ p ∣ m ∧ card G = p ^ n * m

def is_sylow_subgroup [fintype G] (H : subgroup G) := 
    ∃ p : ℕ, is_sylow_subgroup_p H p

--mine

-- is giving G as an input necessary?
-- has a type problem- I need it to recognise that the set is finite
-- as G is finite the set of subsets is also finite

-- def set_of_sylow_subgroups (p : ℕ) [fintype G] : finset (subgroup G) :=
--   { val := _,
--     nodup := _
--     }


-- doesn't return finset
def set_of_sylow_subgroups (p : ℕ) [fintype G] : set (subgroup G) :=
  { H | is_sylow_subgroup_p H p }


def set_of_conjug_subgroups [fintype G] (H : subgroup G) : set (subgroup G) :=
  { J | subgroups_are_conj H J ∧ is_sylow_subgroup J }


def all_left_cosets [fintype G] (H : subgroup G) : finset (subgroup G) :=
  ({ K | ∃ g : G, left_coset g H = K }.finite).to_finset


-- do I need to force finset to get index?
-- if i don't enforce all_left_cosets being finite then this becomes noncomputable
def index_of_subgroup [fintype G] (H : subgroup G) : ℕ :=
  finset.card (all_left_cosets H)

-- why is this noncomputable ??
def index_by_lagranges [fintype G] (H : subgroup G) : ℕ :=
  card G / card H


/-- Second Sylow theorem -/
-- removed (hdvd : p ^ n ∣ card G) from inputs - hG covers this
theorem sylow_p_subgroups_conjugate [fintype G] {p m n : ℕ} (hp : p.prime)
  (hG : card G = p ^ n * m) (hDiv : ¬ p ∣ m) (H : subgroup G)
  (h₁ : is_sylow_subgroup_p H p)
    : set_of_conjug_subgroups H = set_of_sylow_subgroups p :=
begin

  sorry,
end


/-- Alternative formulation of second sylow theorem -/
-- from kbuzzards group theory game
theorem sylow_two [fintype G] {p m n: ℕ} (hp : p.prime) (hG : card G = p ^ n * m)
 (hdiv : ¬ p ∣ m) (H K : subgroup G) (h₁ : is_sylow_subgroup_p H p) (h₂ : is_sylow_subgroup_p K p) : 
∃ (g : G), subgroups_are_conj H K :=
begin
  have h₃ : ¬ index_of_subgroup K = 0,
  {
    -- need to show set of left cosets of H is a K-set

    sorry,
  },



  -- let H' be the set of left cosets of H
  -- let K act on H' by y(xH) = (yx)H, y ∈ K, (x is forming the coset from H to H')
  -- then H' is a K-set     -- what does this mean?
  -- some theorem says |K'| ≡ |H'| (mod p) and |H'| = (G : H)  not div by p
  -- so |K'| ≠ 0 -- index K ≠ 0

  -- let xH ∈ K'
  -- then yxH = xH, ∀ y ∈ K     so x⁻¹yxH = H, ∀ y ∈ K 
  -- so x⁻¹Hx ≤ K
  -- since |H| = |K|, x⁻¹Hx = K so are conjugate subgroups



  sorry,
end



/-- Third Sylow theorem -/
-- As defined at the top of the file
/-
Let `nₚ` be the number of Sylow `p`-subgroups of `G`, then `nₚ` divides the index of the Sylow
`p`-subgroup, `nₚ ≡ 1 [MOD p]`, and `nₚ` is equal to the index of the normalizer of the Sylow
`p`-subgroup in `G`.

- Index is the number of left cosets
-/

/- In my lecture notes, third Sylow theorem is only the second statement. Will begin with that -/


theorem sylow_p_subgroups_size_div_index [fintype G] {p m n nₚ : ℕ} (hp : p.prime)
  (hdvd : p ^ n ∣ card G) (hG : card G = p ^ n * m) (hDiv : ¬ p ∣ m) (A : subgroup G)
  (h₁ : is_sylow_subgroup A) -- nₚ = ord sylₚ(G) 
  : nₚ ∣ index_of_subgroup A :=
begin
  sorry,
end

theorem sylow_p_subgroups_size_congr_1modp [fintype G] {p m n nₚ : ℕ} (hp : p.prime)
  (hdvd : p ^ n ∣ card G) (hG : card G = p ^ n * m) (hDiv : ¬ p ∣ m) -- nₚ = ord sylₚ(G) 
  : nₚ ≡ 1 [MOD p] :=
begin
  sorry,
end


end sylow

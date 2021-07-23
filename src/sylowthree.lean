-- import group_theory.sylow
import tactic
import sylowtwo

open equiv fintype finset mul_action function nat sylow
open subgroup quotient_group
universe u
variables {G : Type u} [group G]

open_locale classical

/-
* Let `nₚ` be the number of Sylow `p`-subgroups of `G`, then `nₚ` divides the index of the Sylow
  `p`-subgroup, `nₚ ≡ 1 [MOD p]`, and `nₚ` is equal to the index of the normalizer of the Sylow
  `p`-subgroup in `G`.
  -/

-- def set_of_conjug_subgroups [fintype G] (L : subgroup G) : set (subgroup G) :=
--   { J | subgroups_are_conj L J ∧ ∃ p : ℕ, is_sylow_subgroup J p }

def set_of_sylow_subgroups [fintype G] {p m n : ℕ} (hp : p.prime) (hG : card G = p ^ n * m) 
  (hndiv: ¬ p ∣ m) : finset (subgroup G) :=
  { L | is_sylow_subgroup L hp hG hndiv }

def num_p_subgroups [fintype G] {p m n: ℕ} (hp : p.prime) (hG : card G = p ^ n * m) 
  (hndiv: ¬ p ∣ m) : ℕ := card (set_of_sylow_subgroups hp hG hndiv)

theorem sylow_three [fintype G] {p m n nₚ : ℕ} (hp : p.prime) (hG : card G = p ^ n * m) 
  (hndiv: ¬ p ∣ m) (h₁ : nₚ = num_p_subgroups hp hG hndiv) : nₚ ≡ 1 [MOD p] :=
begin
  sorry,
end
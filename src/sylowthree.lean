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

def num_p_subgroups (p : ℕ) : ℕ 

theorem sylow_three {p nₚ : ℕ} (h₁ : nₚ = num_p_subgroups p) : nₚ ≡ 1 [MOD p] :=
begin
  sorry,
end
import data.nat.prime
import number_theory.padics.padic_norm

lemma factors_mul (p q : ℕ) : (p * q).factors ~ p.factors ++ q.factors := 
begin
  sorry,
end

lemma factors_prime_pow_eq_repeat_prime_pow (p y : ℕ) (hp : p.prime) : list.repeat p y = (p ^ y).factors :=
begin
  haveI : fact p.prime := ⟨hp⟩,
  induction y,
  { simp [pow_zero, nat.factors_one] },
  { 
    apply list.repeat_perm.1 (list.perm.trans _ (factors_mul p (p ^ y_n)).symm),
    simp [nat.factors_prime hp, y_ih] }
end

lemma valuation_prime_pow_eq_pow {p y : ℕ} (hp : p.prime) : y = padic_val_nat p (p ^ y) :=
begin
  haveI : fact p.prime := ⟨hp⟩,
  rw [padic_val_nat_eq_factors_count p, ← @factors_prime_pow_eq_repeat_prime_pow p y hp, ← (list.count_repeat p y).symm],
end


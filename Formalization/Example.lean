import Mathlib

/-!
# Example: a Phase-1 scaffold

**Source:** Euclid, *Elements*, Book IX, Proposition 20.

**Informal statement:** There are infinitely many primes.

This file is a template. It shows what a scaffold looks like before Phase 2 fills in the proofs.
-/

namespace Formalization.Example

open Nat

/-- For every `n`, the smallest prime factor of `n ! + 1` is greater than `n`.

Proof sketch: `p ∣ n ! + 1`. If `p ≤ n`, then `p ∣ n !`, so `p ∣ 1`. That contradicts `p` being prime. -/
lemma minFac_factorial_succ_gt (n : ℕ) : n < (n ! + 1).minFac := by
  sorry

-- STATEMENT FROZEN
/-- **Euclid.** For every `n` there is a prime `p ≥ n`.

Proof sketch: take `p := (n ! + 1).minFac`. It is prime because `n ! + 1 ≠ 1`,
and `p > n` by `minFac_factorial_succ_gt`. -/
theorem exists_prime_ge (n : ℕ) : ∃ p, n ≤ p ∧ p.Prime := by
  sorry

end Formalization.Example

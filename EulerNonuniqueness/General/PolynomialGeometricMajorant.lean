import Mathlib

noncomputable section

namespace EulerNonuniqueness.General

theorem prod_natCast_add_le_geometric (shifts : Finset ℕ) (power : ℕ) :
    (∏ shift ∈ shifts, (power + shift : ℝ)) ≤
      (2 : ℝ) ^ (∑ shift ∈ shifts, shift) * ((2 : ℝ) ^ shifts.card) ^ power := by
  have bound (shift : ℕ) : (power + shift : ℝ) ≤ (2 : ℝ) ^ (power + shift) := by
    exact_mod_cast (Nat.lt_two_pow_self (n := power + shift)).le
  have actual := Finset.prod_le_prod (s := shifts)
    (fun shift _ => show 0 ≤ (power + shift : ℝ) by positivity) (fun shift _ => bound shift)
  apply actual.trans_eq
  calc
    (∏ shift ∈ shifts, (2 : ℝ) ^ (power + shift)) =
        ∏ shift ∈ shifts, ((2 : ℝ) ^ power * (2 : ℝ) ^ shift) := by simp_rw [pow_add]
    _ = (∏ _shift ∈ shifts, (2 : ℝ) ^ power) * (∏ shift ∈ shifts, (2 : ℝ) ^ shift) :=
      Finset.prod_mul_distrib
    _ = _ := by
      rw [Finset.prod_const, Finset.prod_pow_eq_pow_sum, ← pow_mul, Nat.mul_comm power shifts.card, pow_mul]
      ring

theorem quadratic_natCast_degree_le_geometric (power : ℕ) :
    (power + 2 : ℝ) * (power + 3 : ℝ) ≤ 32 * (4 : ℝ) ^ power := by
  have bound := prod_natCast_add_le_geometric ({2, 3} : Finset ℕ) power
  norm_num at bound ⊢
  exact bound

theorem cubic_natCast_degree_le_geometric (power : ℕ) :
    (power + 2 : ℝ) * (power + 3 : ℝ) * (power + 4 : ℝ) ≤ 512 * (8 : ℝ) ^ power := by
  have bound := prod_natCast_add_le_geometric ({2, 3, 4} : Finset ℕ) power
  norm_num [mul_assoc] at bound ⊢
  exact bound

end EulerNonuniqueness.General

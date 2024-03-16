import Lean4.fraction

namespace FractionEqualities

lemma one_sub_inverse_of_add_one {n : ℝ} (hn : n + 1 ≠ 0) :
    1 - 1 / (n + 1) = n / (n + 1) := by
  nth_rewrite 1 [←div_self hn]
  rw [div_sub_div_same, add_sub_cancel]

lemma frac_cancel {a b c : ℝ} (hb : b ≠ 0) : (a / b) * (b / c) = a / c := by
  rw [mul_div, div_mul_cancel]
  exact hb

lemma frac_cancel' {a b c : ℝ} (hb : b ≠ 0) : (b / a) * (c / b) = c / a := by
  rw [mul_comm]
  exact frac_cancel hb

lemma one_sub_frac {a b : ℝ} (hb : b + 1 ≠ 0) : (1 - (a + 1)/(b+1)) = (b - a) / (b + 1) := by
  nth_rewrite 1 [←div_self hb]
  rw [div_sub_div_same]
  congr 1
  ring

lemma frac_special {a b c : ℝ} (hbc : b ≠ c) (hc : c + 1 ≠ 0) :
    (a + (b + 1)) / (c + 1) = (1 - (b + 1) / (c + 1)) * (a / (c - b)) + (b + 1) / (c + 1) := by
  rw [one_sub_frac hc, frac_cancel']
  · exact (div_add_div_same _ _ _).symm
  · exact sub_ne_zero_of_ne hbc.symm

/--
  For any `i n : ℕ` with `i > 0` and `i ≤ (n + 1) * i`, we have that `1 / (n + 1) = i / ((n + 1) * i)`.
-/
lemma cancel_common_factor {i n : ℕ} (i_pos : 0 < i) (hi_n : (i - 1).succ ≤ ((n+1) * i - 1).succ) :
    Fraction.ofPos (Nat.succ_pos n) = Fraction (Nat.succ_pos _) hi_n := by
  simp
  have : (↑(i - 1) : ℝ) + 1 = i := by
    nth_rewrite 1 [←Nat.succ_pred_eq_of_pos i_pos]
    simp
    rw [←Nat.cast_succ]
    rw [Nat.succ_pred_eq_of_pos i_pos]

  rw [this]
  have : (↑((n+1)* i - 1) : ℝ) + 1 = (↑n+1)*↑i := by
    rw [←Nat.cast_succ n, ←Nat.cast_mul]
    nth_rewrite 1 [←Nat.succ_pred_eq_of_pos (mul_pos (Nat.succ_pos n) i_pos)]
    simp
    rw [←Nat.cast_succ]
    rw [Nat.succ_pred_eq_of_pos (mul_pos (Nat.succ_pos n) i_pos)]
    simp

  rw [this, div_mul_left _]
  exact (one_div _).symm
  exact ne_of_gt (Nat.cast_pos.mpr i_pos)

end FractionEqualities

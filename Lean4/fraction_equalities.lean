import Lean4.fraction

-- TODO: Refactor this in some way?

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

end FractionEqualities

import Mathlib.Topology.UnitInterval

open scoped unitInterval

namespace unitIAux

lemma double_pos_of_pos {T : I} (hT₀ : 0 < T) : 0 < (2 * T : ℝ) :=
  mul_pos zero_lt_two hT₀
lemma double_sigma_pos_of_lt_one {T : I} (hT₁ : T < 1) : 0 < (2 * (1 - T) : ℝ) :=
  mul_pos zero_lt_two (by {simp; exact hT₁})

lemma double_mem_I {t : I} (ht : ↑t ≤ (2⁻¹ : ℝ)) : 2 * (t : ℝ) ∈ I := by
  constructor
  exact mul_nonneg zero_le_two t.2.1
  calc
    2 * (t : ℝ) ≤ 2 * 2⁻¹ := by exact (mul_le_mul_left zero_lt_two).mpr ht
              _ = 1 := by norm_num

lemma double_sub_one_mem_I {t : I} (ht : (2⁻¹ : ℝ) ≤ ↑t) : 2 * (t : ℝ) - 1 ∈ I := by
  constructor
  calc 0 = 2 * (2⁻¹ : ℝ) - 1 := by norm_num
       _ ≤ 2 * ↑t - 1 := sub_le_sub_right ((mul_le_mul_left (by norm_num)).mpr ht) 1
  calc 2 * (t : ℝ) - 1 ≤ 2 * 1 - 1 := by exact sub_le_sub_right ((mul_le_mul_left (by norm_num)).mpr t.2.2) 1
                     _ = 1 := by norm_num

lemma interp_left_le_of_le (T : I) {a b : I} (hab : a ≤ b) : (σ T : ℝ) * ↑a + ↑T ≤ (σ T : ℝ) * ↑b + ↑T := by
  apply add_le_add_right
  apply mul_le_mul
  rfl
  exact hab
  exact a.2.1
  exact (σ T).2.1

end unitIAux

import Mathlib.Topology.Connected.PathConnected

open scoped unitInterval

namespace unitIAux

lemma zero_le (T : I) : ⟨0, unitInterval.zero_mem⟩ ≤ T := Subtype.coe_le_coe.mp T.2.1
lemma le_one (T : I) : T ≤ ⟨1, unitInterval.one_mem⟩:= Subtype.coe_le_coe.mp T.2.2

lemma double_pos_of_pos {T : I} (hT₀ : 0 < T) : 0 < (2 * T : ℝ) :=
  mul_pos two_pos hT₀
lemma double_sigma_pos_of_lt_one {T : I} (hT₁ : T < 1) : 0 < (2 * (1 - T) : ℝ) :=
  mul_pos two_pos (by {simp; exact hT₁})

lemma double_mem_I {t : I} (ht : ↑t ≤ (2⁻¹ : ℝ)) : 2 * (t : ℝ) ∈ I := by
  constructor
  exact mul_nonneg zero_le_two t.2.1
  calc 2 * (t : ℝ)
      _ ≤ 2 * 2⁻¹ := (mul_le_mul_left two_pos).mpr ht
      _ = 1 := by norm_num

lemma double_sub_one_mem_I {t : I} (ht : (2⁻¹ : ℝ) ≤ ↑t) : 2 * (t : ℝ) - 1 ∈ I := by
  constructor
  calc 0 = 2 * (2⁻¹ : ℝ) - 1 := by norm_num
       _ ≤ 2 * ↑t - 1        := sub_le_sub_right ((mul_le_mul_left (by norm_num)).mpr ht) 1
  calc 2 * (t : ℝ) - 1
      _ ≤ 2 * 1 - 1 := sub_le_sub_right ((mul_le_mul_left (by norm_num)).mpr t.2.2) 1
      _ = 1         := by norm_num

lemma interp_left_le_of_le (T : I) {a b : I} (hab : a ≤ b) : (σ T : ℝ) * ↑a + ↑T ≤ (σ T : ℝ) * ↑b + ↑T := by
  apply add_le_add_right
  apply mul_le_mul
  rfl
  exact hab
  exact a.2.1
  exact (σ T).2.1

section

noncomputable section

lemma half_mem_I : (2⁻¹ : ℝ) ∈ I :=
⟨inv_nonneg.mpr zero_le_two, inv_le_one one_le_two⟩

abbrev half_I : I := ⟨(2⁻¹ : ℝ), half_mem_I⟩

lemma has_T_half {t₀ t₁ : I} (γ : Path t₀ t₁) (ht₀ : ↑t₀ < (2⁻¹ : ℝ)) (ht₁ : ↑t₁ > (2⁻¹ : ℝ)) :
  ∃ (T : I),  0 < T ∧ T < 1 ∧ (γ T) = half_I := by

  have : γ.toFun 0 ≤ half_I := by rw [γ.source']; exact Subtype.coe_le_coe.mp (le_of_lt ht₀)
  have h₀ : ∃ (t : I), γ t ≤ half_I := ⟨0, this⟩
  have : half_I ≤ γ.toFun 1 := by rw [γ.target']; exact Subtype.coe_le_coe.mp (le_of_lt ht₁)
  have h₁ : ∃ (t : I), half_I ≤ γ t := ⟨1, this⟩
  have hy := Set.mem_range.mp (mem_range_of_exists_le_of_exists_ge γ.continuous_toFun h₀ h₁)

  cases' hy with T hT
  use T
  have hT₀ : 0 ≠ T := by
    rintro ⟨rfl⟩
    apply lt_irrefl (t₀ : ℝ)
    calc (t₀ : ℝ)
        _ < 2⁻¹       := ht₀
        _ = (γ 0 : ℝ) := Subtype.coe_inj.mpr hT.symm
        _ = ↑t₀       := Subtype.coe_inj.mpr γ.source'

  have hT₁ : T ≠ 1 := by
    rintro ⟨rfl⟩
    apply lt_irrefl (t₁ : ℝ)
    calc (t₁ : ℝ)
      _ = (γ 1 : ℝ) := Subtype.coe_inj.mpr γ.target'.symm
      _ = half_I    := Subtype.coe_inj.mpr hT
      _ < ↑t₁       := ht₁

  exact ⟨lt_iff_le_and_ne.mpr ⟨T.2.1, hT₀⟩, lt_iff_le_and_ne.mpr ⟨T.2.2, hT₁⟩, hT⟩
end

end

end unitIAux

import Mathlib.Topology.Connected.PathConnected

open scoped unitInterval
noncomputable section

/--
For any natural numbers `i n : ℕ` such that `n` is positive and `i ≤ n`, we have that the fraction
`i/n : ℝ` lives in the unit interval
-/
@[reducible]
def Fraction {i n : ℕ} (hn : 0 < n) (hi : i ≤ n) : I :=
  ⟨(i : ℝ)/(n : ℝ), ⟨div_nonneg (Nat.cast_nonneg i) (Nat.cast_nonneg n), (div_le_one ((@Nat.cast_pos ℝ _ _ n).mpr hn)).mpr (Nat.cast_le.mpr hi)⟩⟩

namespace Fraction

/--
For any positive number `n : ℕ`, we have the fraction `1/n : ℝ` in the unit interval
-/
@[reducible]
def ofPos {n : ℕ} (hn : 0 < n) : I := Fraction hn (Nat.succ_le_iff.mpr hn)

@[simp]
lemma Fraction_coe {i n : ℕ} (hn : 0 < n) (hi : i ≤ n) : (Fraction hn hi : ℝ) = (i/n : ℝ) := rfl
@[simp]
lemma ofPos_coe {n : ℕ} (hn : 0 < n) : ((ofPos hn) : ℝ) = (1/n : ℝ) := by simp

/--
For any postive `n : ℕ`, we have that `0/n = n`.
-/
lemma eq_zero {n : ℕ} (n_pos : 0 < n) : Fraction n_pos (Nat.zero_le n) = 0 := by
  ext
  rw [Fraction_coe]
  simp

/--
For any postive `n : ℕ`, we have that `n/n = n`.
-/
lemma eq_one {n : ℕ} (n_pos : 0 < n) : Fraction n_pos (le_refl n) = 1 := by
  ext
  rw [Fraction_coe, div_self]
  simp
  exact Nat.cast_ne_zero.mpr (ne_of_gt n_pos)

/--
For any `i n : ℕ` with `0 < i ≤ n`, we have that `i/n * 1/i` = `1/n` as members of `I`.
-/
lemma mul_inv {i n : ℕ} (i_pos : 0 < i) (hi_n : i ≤ n) :
    (Fraction (lt_of_lt_of_le i_pos hi_n) hi_n) * (ofPos i_pos) = (ofPos (lt_of_lt_of_le i_pos hi_n)) := by
  apply Subtype.coe_inj.mp
  simp
  calc (i : ℝ)/n * (↑i)⁻¹
    _ = (i * (↑i)⁻¹)/↑n  := div_mul_eq_mul_div (i : ℝ) n i⁻¹
    _ = 1/n              := by rw [mul_inv_cancel (Nat.cast_ne_zero.mpr (ne_of_lt i_pos).symm)]
    _ = (↑n)⁻¹           := one_div (n : ℝ)

/--
For any `n i : ℕ` with `0 < i ≤ n`, we have that `0 < i/n`.
-/
lemma pos_of_pos {n i : ℕ} (hi : 0 < i) (hn : i ≤ n) : 0 < Fraction (lt_of_lt_of_le hi hn) hn :=
  Subtype.coe_lt_coe.mp (div_pos (Nat.cast_pos.mpr hi) (Nat.cast_pos.mpr (lt_of_lt_of_le hi hn)))

/--
For any `n i : ℕ` with `0 ≤ i < n`, we have that `i/n < 1`.
-/
lemma lt_one_of_lt {n i : ℕ} (hi : 0 ≤ i) (hn : i < n) : Fraction (lt_of_le_of_lt hi hn) (le_of_lt hn) < 1 :=
  Subtype.coe_lt_coe.mp ((div_lt_one (Nat.cast_pos.mpr (lt_of_le_of_lt hi hn))).mpr (Nat.cast_lt.mpr hn))

/-
For any positive `n : ℕ`, we have that `0 < 1/n`.
-/
lemma ofPos_pos {n : ℕ} (hn : 0 < n) : 0 < ofPos hn := pos_of_pos zero_lt_one (Nat.succ_le_iff.mpr hn)

/-
For any `n : ℕ` with `n > 1`, we have that `1/n < 1`.
-/
lemma ofPos_lt_one {n : ℕ} (hn : 1 < n) : ofPos (lt_trans zero_lt_one hn) < 1 := lt_one_of_lt zero_le_one hn

/-
For any `n m : ℕ` with `m < n`, we have that `m/n ≤ (m+1) ≤ n`
-/
lemma lt_frac_succ {n m : ℕ} (hn : m < n) :
    Fraction (lt_of_le_of_lt (Nat.zero_le m) hn) (le_of_lt hn) <
    Fraction (lt_of_le_of_lt (Nat.zero_le m) hn) (Nat.succ_le_of_lt hn) := by
  simp
  exact div_lt_div (by linarith) (by linarith) (by linarith)
    (Nat.cast_pos.mpr (lt_of_le_of_lt (Nat.zero_le m) hn))

end Fraction

import Lean4.SplitPath.split_dipath
import Lean4.fraction
import Lean4.fraction_equalities

/-
  This file contains lemmas about splitting a (di)path into two parts,
  and how their concatenation relates to the original (di)path
-/

open scoped unitInterval
open SplitDipath Set

noncomputable section

universe u

variable {X : Type u} [DirectedSpace X] {x₀ x₁ : X}

namespace SplitProperties


--TODO: Rework some of these statement to make them more general: that should make proving the
-- specfic versions easier.

/-! ### General -/

lemma firstPart_cast {x₀' x₁' : X} (γ : Dipath x₀ x₁) (hx₀ : x₀' = x₀) (hx₁ : x₁' = x₁) (T : I) :
  (FirstPartDipath (γ.cast hx₀ hx₁) T) = (FirstPartDipath γ T).cast hx₀ rfl := rfl

lemma secondPart_cast {x₀' x₁' : X} (γ : Dipath x₀ x₁) (hx₀ : x₀' = x₀) (hx₁ : x₁' = x₁) (T : I) :
  (SecondPartDipath (γ.cast hx₀ hx₁) T) = (SecondPartDipath γ T).cast rfl hx₁ := rfl

lemma firstPart_eq_of_split_point_eq (γ : Dipath x₀ x₁) {T T' : I} (hT : T = T') :
  (FirstPartDipath γ T) = (FirstPartDipath γ T').cast rfl (congr_arg γ hT) := by subst_vars; rfl

lemma secondPart_eq_of_split_point_eq (γ : Dipath x₀ x₁) {T T' : I} (hT : T = T') :
  (SecondPartDipath γ T) = (SecondPartDipath γ T').cast (congr_arg γ hT) rfl := by subst_vars; rfl

lemma firstPart_eq_of_point_eq (γ : Dipath x₀ x₁) {T T': I} (h : T = T') (t : I) :
  (FirstPartDipath γ T) t = (FirstPartDipath γ T') t := by subst_vars; rfl

lemma secondPart_eq_of_point_eq (γ : Dipath x₀ x₁) {T T': I} (h : T = T') (t : I) :
  (SecondPartDipath γ T) t = (SecondPartDipath γ T') t := by subst_vars; rfl

lemma interval_cast {γ : Dipath x₀ x₁} {A : Set X} {a b a' b' : I} (h_im : A = γ '' Icc a b)
      (ha : a' = a) (hb : b' = b) :
    A = γ '' Icc a' b' := by subst_vars; rfl


/-! ### First Part -/

lemma firstPart_image (γ : Dipath x₀ x₁) (T a b : I) (h_ab : a ≤ b):
    (FirstPartDipath γ T) '' Icc a b = γ '' Icc (T * a) (T * b) := by
  ext z
  constructor
  · rintro ⟨t, t_a_b, ht⟩
    rw [first_part_apply] at ht
    use T * t
    constructor
    constructor
    · exact Subtype.coe_le_coe.mp $ mul_le_mul_of_nonneg_left (Subtype.coe_le_coe.mpr t_a_b.1) T.2.1
    · exact Subtype.coe_le_coe.mp $ mul_le_mul_of_nonneg_left (Subtype.coe_le_coe.mpr t_a_b.2) T.2.1
    · exact ht
  · rintro ⟨t, t_Ta_Tb, ht⟩
    by_cases h : T = 0
    · use a
      constructor
      · simp; exact h_ab
      · show γ (T * a) = z
        simp [h] at t_Ta_Tb
        rw [h, zero_mul]
        exact t_Ta_Tb ▸ ht
    have hT : 0 < T := lt_of_le_of_ne unitInterval.nonneg' (show T ≠ 0 by exact h).symm
    have h₁ : (a : ℝ) ≤ (t / T : ℝ) :=
      (le_div_iff $ Subtype.coe_lt_coe.mpr hT).mpr $ mul_comm (a : ℝ) T ▸ Subtype.coe_le_coe.mpr t_Ta_Tb.1
    have h₂ : (t / T : ℝ) ≤ b :=
      (div_le_iff $ Subtype.coe_lt_coe.mpr hT).mpr $ mul_comm (b : ℝ) T ▸ Subtype.coe_le_coe.mpr t_Ta_Tb.2
    use ⟨t / T, le_trans a.2.1 h₁, le_trans h₂ b.2.2⟩

    constructor
    · exact ⟨h₁, h₂⟩
    · rw [first_part_apply]
      convert ht using 2
      simp
      apply Subtype.coe_inj.mp
      show (T : ℝ) * (t / T) = t
      rw [mul_div_left_comm, div_self]
      · exact mul_one (t : ℝ)
      · exact unitInterval.coe_ne_zero.mpr h

lemma firstPart_range (γ : Dipath x₀ x₁) (T : I) :
    range (FirstPartDipath γ T) = (γ '' Icc 0 T) := by
  rw [Dipath.range_eq_image_I _]
  convert firstPart_image γ T 0 1 zero_le_one <;> norm_num

lemma firstPart_range_interval (γ : Dipath x₀ x₁) {n : ℕ} (h : 0 < n) :
    range (FirstPartDipath γ (Fraction.ofPos h)) = γ ''  Icc 0 (Fraction.ofPos h) :=
  firstPart_range γ (Fraction.ofPos h)

lemma firstPart_range_interval_coe (γ : Dipath x₀ x₁) {n : ℕ} (h : 0 < n):
    range (FirstPartDipath γ (Fraction.ofPos h)) = γ.extend ''  Icc 0 (1/(↑n)) := by
  rw [firstPart_range_interval γ h, ←Dipath.image_extend_eq_image, Fraction.ofPos_coe]
  rfl

/--
If `γ` is a path, then the image of `[i/(d+1), (i+1)/(d+1)]` under `γ` split at `(d+1)/(n+1)` is the
image of `[i/(n+1), (i+1)/(n+1)]` under `γ`
-/
lemma firstPart_range_interval_partial (γ : Dipath x₀ x₁) {n d i : ℕ} (hd : d.succ < n.succ) (hi : i < d.succ) :
  (FirstPartDipath γ (Fraction (Nat.succ_pos n) (le_of_lt hd))) '' Icc -- First part at (d + 1)/(n + 1)
    (Fraction (Nat.succ_pos d) (le_of_lt hi)) -- frac i/(d+1)
    (Fraction (Nat.succ_pos d) (Nat.succ_le_of_lt hi)) -- frac (i+1)/(d+1)
    = γ ''  Icc
    (Fraction (Nat.succ_pos n) (le_of_lt (lt_trans hi hd))) -- frac i/(n+1)
    (Fraction (Nat.succ_pos n) (Nat.succ_le_of_lt (lt_trans hi hd))) -- frac (i+1)/(n+1)
  := by
  convert firstPart_image γ (Fraction (Nat.succ_pos n) (le_of_lt hd))
    (Fraction (Nat.succ_pos d) (le_of_lt hi)) (Fraction (Nat.succ_pos d) (Nat.succ_le_of_lt hi))
    (show _ ≤ _ by simp; apply div_le_div <;> linarith) <;>
  simp [Fraction] <;>
  apply Subtype.coe_inj.mp <;>
  simp <;>
  refine (FractionEqualities.frac_cancel' ?_).symm <;>
  rw [←Nat.cast_succ] <;>
  exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero d)

/--
If `γ` is a path, then the image of `[i/(d+1), (i+1)/(d+1)]` under `γ` split at `(d+1)/(n+1)` is the
image of `[i/(n+1), (i+1)/(n+1)]` under `γ`.
-/
lemma firstPart_range_interval_partial_coe (γ : Dipath x₀ x₁) {n d i : ℕ} (hd : d.succ < n.succ) (hi : i < d.succ) :
    (FirstPartDipath γ (Fraction (Nat.succ_pos n) (le_of_lt hd))).extend '' Icc (↑i/(↑d+1)) ((↑i+1)/(↑d+1))
      = γ.extend ''  Icc (↑i/(↑n+1)) ((↑i+1)/(↑n+1)) := by
  have := firstPart_range_interval_partial γ hd hi
  rw [←Dipath.image_extend_eq_image] at this
  rw [←Dipath.image_extend_eq_image] at this
  convert this <;> exact (Nat.cast_succ _).symm

/-! ### Second Part -/

lemma secondPart_image (γ : Dipath x₀ x₁) (T a b : I) (h_ab : a ≤ b):
    (SecondPartDipath γ T) '' Icc a b = γ '' Icc
      ⟨σ T * a + T, interp_left_mem_I T a⟩
      ⟨σ T * b + T, interp_left_mem_I T b⟩ := by
  ext z
  constructor
  · rintro ⟨t, t_a_b, ht⟩
    rw [second_part_apply] at ht
    use ⟨σ T * t + T, interp_left_mem_I T t⟩
    exact ⟨⟨unitIAux.interp_left_le_of_le T t_a_b.1, unitIAux.interp_left_le_of_le T t_a_b.2⟩, ht⟩

  · rintro ⟨t, t_Ta_Tb, ht⟩
    by_cases h : T = 1
    · use a
      constructor
      · simp; exact h_ab
      · show γ (_) = z
        simp [h] at t_Ta_Tb
        simp [t_Ta_Tb] at ht
        simp [h, ht]
    have hT : T < 1 := lt_of_le_of_ne unitInterval.le_one' (show T ≠ 1 by exact h)
    have : (T : ℝ) < 1 := Subtype.coe_lt_coe.mpr hT
    have : (σ T : ℝ) > 0 := show (1 - T : ℝ) > 0 by linarith

    have h₁ : (a : ℝ) ≤ ((t - T) / (σ T) : ℝ) := by
      apply (le_div_iff this).mpr
      rw [mul_comm]
      have : (σ T : ℝ) * a  + T ≤ t := t_Ta_Tb.1
      linarith
    have h₂ : ((t - T) / (1 - T) : ℝ) ≤ b := by
      apply (div_le_iff this).mpr
      rw [mul_comm]
      have : (t : ℝ) ≤ (σ T : ℝ) * b + T := t_Ta_Tb.2
      linarith

    use ⟨(t - T) / (1 - T), le_trans a.2.1 h₁, le_trans h₂ b.2.2⟩

    constructor
    · exact ⟨h₁, h₂⟩
    · rw [second_part_apply]
      convert ht using 2
      simp
      apply Subtype.coe_inj.mp
      show (σ T : ℝ) * ((t-T)/(σ T)) + T = t
      rw [mul_div_left_comm, div_self]
      ring
      exact ne_of_gt this

lemma secondPart_range (γ : Dipath x₀ x₁) (T : I) :
    range (SecondPartDipath γ T) = γ '' Icc T 1  := by
  rw [Dipath.range_eq_image_I _]
  convert secondPart_image γ T 0 1 zero_le_one using 3 <;> simp

/--
  When γ is a dipath, an we split it on the intervals [0, 1/(n+1)] and [1/(n+1), 1], then the image of γ of
  [(i+1)/(n+1), (i+2)/(n+1)] is equal to the image the second part of γ of [i/n, (i+1)/n]
-/
lemma secondPart_range_interval (γ : Dipath x₀ x₁) {i n : ℕ} (hi : i < n) (hn : 0 < n):
    (SecondPartDipath γ (Fraction.ofPos (Nat.succ_pos n))) '' Icc
      (Fraction hn (le_of_lt hi)) (Fraction hn (Nat.succ_le_of_lt hi)) =
    γ ''  Icc (Fraction (Nat.succ_pos n) (show i+1 ≤ n+1 by exact (le_of_lt (Nat.succ_lt_succ hi))))
              (Fraction (Nat.succ_pos n) (show i+2 ≤ n+1 by exact Nat.succ_lt_succ (Nat.succ_le_of_lt hi))) := by

  have h₁ : (n : ℝ) * ((n : ℝ) + 1)⁻¹ = (1 - ((n : ℝ) + 1)⁻¹)
  · have : (n + 1 : ℝ) ≠ 0 := ne_of_gt (add_pos (Nat.cast_pos.mpr hn) one_pos)
    nth_rewrite 2 [(div_self this).symm]
    ring

  have h₂ : (n + 1 : ℝ)⁻¹ = (1 - ((n : ℝ) + 1)⁻¹) * (↑n)⁻¹
  · have : (0 : ℝ) < ↑n := by exact Nat.cast_pos.mpr hn
    calc (n + 1 : ℝ)⁻¹
      _ = (n + 1 : ℝ)⁻¹ * (n : ℝ) / (n : ℝ) := (mul_div_cancel (n + 1 : ℝ)⁻¹ (by linarith)).symm
      _ = ↑n * (↑n + 1)⁻¹ * (↑n)⁻¹ := by ring
      _ =  (1 - (↑n + 1)⁻¹) * (↑n)⁻¹ := by rw [h₁]

  apply interval_cast (secondPart_image γ (Fraction.ofPos (Nat.succ_pos n)) _ _ (Fraction.lt_frac_succ hi))
  · simp
    calc (i + 1 : ℝ)/(↑n + 1)
      _ = ↑i/(↑n + 1) + 1/(↑n+1)                          := by ring
      _ = ↑i/(↑n + 1) + (↑n + 1)⁻¹                        := by rw [one_div]
      _ = (↑n + 1)⁻¹ * ↑i + (↑n + 1)⁻¹                    := by rw [div_eq_inv_mul]
      _ = (1 - (↑n + 1)⁻¹) * (↑n)⁻¹ * (↑i) + (↑n + 1)⁻¹   := by rw [←h₂]
      _ = (1 - (↑n + 1)⁻¹) * ((↑n)⁻¹ * (↑i)) + (↑n + 1)⁻¹ := by ring
      _ = (1 - (↑n + 1)⁻¹) * (↑i / ↑n) + (↑n + 1)⁻¹       := by rw [←div_eq_inv_mul (i : ℝ) ↑n]
  · simp
    calc (i + 2 : ℝ)/(↑n + 1)
      _ = (↑i + 1)/(↑n + 1) + 1/(↑n+1)                        := by ring
      _ = (↑i + 1)/(↑n + 1) + (↑n + 1)⁻¹                      := by rw [one_div]
      _ = (↑n + 1)⁻¹ * (↑i + 1) + (↑n + 1)⁻¹                  := by rw [div_eq_inv_mul]
      _ = (1 - (↑n + 1)⁻¹) * (↑n)⁻¹ * (↑i + 1) + (↑n + 1)⁻¹   := by rw [←h₂]
      _ = (1 - (↑n + 1)⁻¹) * ((↑n)⁻¹ * (↑i + 1)) + (↑n + 1)⁻¹ := by ring
      _ = (1 - (↑n + 1)⁻¹) * ((↑i + 1) / ↑n) + (↑n + 1)⁻¹     := by rw [←div_eq_inv_mul (i + 1 : ℝ) ↑n]

/--
  When γ is a dipath, an we split it on the intervals [0, 1/(n+1)] and [1/(n+1), 1], then the image of γ of
  [(i+1)/(n+1), (i+2)/(n+1)] is equal to the image the second part of γ of [i/n, (i+1)/n].
  Version with interval of real numbers
-/
lemma secondPart_range_interval_coe (γ : Dipath x₀ x₁) {i n : ℕ} (hi : i < n) (hn : 0 < n):
    (SecondPartDipath γ (Fraction.ofPos (Nat.succ_pos n))).extend '' Icc (↑i/↑n) ((↑i+1)/↑n) =
    γ.extend ''  Icc ((↑i+1)/(↑n+1)) ((↑i+1+1)/(↑n+1)) := by
  have := secondPart_range_interval γ hi hn
  rw [←Dipath.image_extend_eq_image] at this
  rw [←Dipath.image_extend_eq_image] at this
  convert this
  exact (Nat.cast_succ i).symm
  exact (Nat.cast_succ i).symm
  exact (Nat.cast_succ n).symm
  rw [←Nat.cast_succ i]
  rw [←Nat.cast_succ i.succ]
  exact (Nat.cast_succ n).symm

/--
  When γ is a dipath, an we split it on the intervals [0, (d+1)/(n+1)] and [(d+1)/(n+1), 1], then the image of γ of
  [(i+d.succ)/(n+1), (i+d.succ+1)/(n+1)] is equal to the image the second part of γ of [(i/(n-d), (i+1)/(n-d)].
-/
lemma secondPart_range_partial_interval (γ : Dipath x₀ x₁) {i d n : ℕ} (hd : d.succ < n.succ) (hi : i < n - d) :
    (SecondPartDipath γ (Fraction (Nat.succ_pos n) (le_of_lt hd))) '' Icc
      (Fraction (Nat.sub_pos_of_lt (Nat.lt_of_succ_lt_succ hd)) (le_of_lt hi)) -- i/(n-d)
      (Fraction (Nat.sub_pos_of_lt (Nat.lt_of_succ_lt_succ hd)) (Nat.succ_le_of_lt hi)) -- (i+1)/(n-d)
      =
    γ ''  Icc
      (Fraction (Nat.succ_pos n) (show i+d.succ ≤ n.succ by
        apply le_of_lt
        have : i < n.succ - d.succ := (Nat.succ_sub_succ n d).symm ▸ hi
        exact lt_tsub_iff_right.mp this
      )) -- (i+d+1)/(n+1)
      (Fraction (Nat.succ_pos n) (show i+d.succ + 1 ≤ n.succ by
        apply Nat.succ_le_of_lt
        have : i < n.succ - d.succ := (Nat.succ_sub_succ n d).symm ▸ hi
        exact lt_tsub_iff_right.mp this
      )) -- (i+d+2)/(n+1)
    := by
  apply interval_cast
    (secondPart_image γ (Fraction (Nat.succ_pos n) (le_of_lt hd)) _ _ (Fraction.lt_frac_succ hi))
  · simp
    have : d < n := Nat.lt_of_succ_lt_succ hd
    rw [Nat.cast_sub (le_of_lt this)]
    apply FractionEqualities.frac_special
    · exact (ne_of_lt (Nat.cast_lt.mpr this))
    · rw [←Nat.cast_succ]
      exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  · simp
    have : d < n := Nat.lt_of_succ_lt_succ hd
    rw [Nat.cast_sub (le_of_lt this)]
    rw [add_assoc]
    rw [add_comm (↑d + 1 : ℝ) 1]
    rw [←add_assoc]
    apply FractionEqualities.frac_special
    · exact (ne_of_lt (Nat.cast_lt.mpr this))
    · rw [←Nat.cast_succ]
      exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)

/--
  When γ is a dipath, an we split it on the intervals [0, (d+1)/(n+1)] and [(d+1)/(n+1), 1], then the image of γ of
  [(i+d.succ)/(n+1), (i+d.succ+1)/(n+1)] is equal to the image the second part of γ of [i/(n-d), (i+1)/(n-d)].
-/
lemma secondPart_range_partial_interval_coe (γ : Dipath x₀ x₁) {i d n : ℕ} (hd : d.succ < n.succ) (hi : i < n - d) :
  (SecondPartDipath γ (Fraction (Nat.succ_pos n) (le_of_lt hd))).extend '' Icc (↑i/(↑n-↑d)) ((↑i+1)/(↑n-↑d))
    = γ.extend ''  Icc ((↑(i+d.succ))/(↑n+1)) ((↑(i+d.succ) + 1)/(↑n+1)) := by
  have := secondPart_range_partial_interval γ hd hi
  rw [←Dipath.image_extend_eq_image] at this
  rw [←Dipath.image_extend_eq_image] at this
  convert this
  · exact (Nat.cast_sub (le_of_lt $ Nat.lt_of_succ_lt_succ hd)).symm
  · exact (Nat.cast_succ _).symm
  · exact (Nat.cast_sub (le_of_lt $ Nat.lt_of_succ_lt_succ hd)).symm
  · exact (Nat.cast_succ _).symm
  · exact (Nat.cast_succ _).symm
  · exact (Nat.cast_succ _).symm

/-! ### Mixed Parts -/

/--
  Splitting a dipath `γ` at `[0, k/n]` and then at `[0, 1/k]` is the same as splitting it at `[0, 1/n]`.
-/
lemma firstPart_of_firstPart (γ : Dipath x₀ x₁) {n k : ℕ} (hkn : k < n) (hk : 0 < k) :
    FirstPartDipath
      (FirstPartDipath γ (Fraction (lt_trans hk hkn) (le_of_lt hkn)))
        (Fraction.ofPos hk) -- 1/k
    = (FirstPartDipath γ (Fraction.ofPos $ lt_trans hk hkn)).cast rfl
      (show γ _ = γ _ by { congr 1; rw [←Fraction.mul_inv hk (le_of_lt hkn)]; rfl }) := by
  ext x
  show γ _ = γ _
  congr 1
  rw [←Fraction.mul_inv hk (le_of_lt hkn)]
  simp
  rw [mul_assoc]

/--
  Splitting a dipath `[0, (k+1)/(n+1)]` and then `[1/(k+1), 1]` is the same as
  splitting it `[1/(n+1), 1]` and then `[0, k/n]`
-/
lemma first_part_of_second_part (γ : Dipath x₀ x₁) {n k : ℕ} (hkn : k < n) (hk : 0 < k) :
  SecondPartDipath
    (FirstPartDipath γ (Fraction (Nat.succ_pos n) (le_of_lt $ Nat.succ_lt_succ hkn))) -- (k+1)/(n+1)
    (Fraction.ofPos (Nat.succ_pos k)) -- 1/(k+1)
  =
  (FirstPartDipath
      (SecondPartDipath γ (Fraction.ofPos (Nat.succ_pos n))) -- 1/(n+1)
      (Fraction (lt_trans hk hkn) (le_of_lt hkn)) -- k/n
  ).cast
    (show γ _ = γ _ by congr 1; apply Subtype.coe_inj.mp; rw [←Fraction.mul_inv (Nat.succ_pos k) (le_of_lt (Nat.succ_lt_succ hkn))]; rfl)
    (show γ _ = γ _ by
      congr 1
      simp
      have : (n : ℝ) > 0 := Nat.cast_pos.mpr (lt_trans hk hkn)
      rw [← one_div, FractionEqualities.one_sub_inverse_of_add_one, FractionEqualities.frac_cancel', ← add_div]
      linarith
      linarith)
    := by
  ext x
  show γ _ = γ _
  congr 1
  simp
  have : (k : ℝ) > 0 := Nat.cast_pos.mpr hk
  have : (n : ℝ) > 0 := Nat.cast_pos.mpr (lt_trans hk hkn)
  rw [←one_div]
  rw [←one_div]
  rw [FractionEqualities.one_sub_inverse_of_add_one _]
  rw [FractionEqualities.one_sub_inverse_of_add_one _]
  rw [mul_comm ((k : ℝ)/(↑k + 1)) (x : ℝ)]
  rw [mul_div, ← add_div, FractionEqualities.frac_cancel']
  rw [← mul_assoc ((n : ℝ) / (n+1 : ℝ)) (k/n : ℝ) (x : ℝ)]
  rw [FractionEqualities.frac_cancel']
  rw [mul_comm ((k : ℝ)/(↑n + 1)) (x : ℝ)]
  rw [mul_div, ← add_div]
  repeat { linarith }

/--
  Splitting a dipath [(k+2)/(n+2), 1] is the same as splitting it [1/(n+2), 1] and then [(k+1)/(n+1), 1]
-/
lemma second_part_of_second_part (γ : Dipath x₀ x₁) {n k : ℕ} (hkn : k < n) :
  SecondPartDipath
    (SecondPartDipath γ (Fraction.ofPos (Nat.succ_pos n.succ))) -- 1/(n+2)
    (Fraction (Nat.succ_pos n) (le_of_lt $ Nat.succ_lt_succ hkn)) -- (k+1)/(n+1)
  =
  (
    SecondPartDipath γ (Fraction (Nat.succ_pos n.succ) (le_of_lt $ Nat.succ_lt_succ (Nat.succ_lt_succ hkn))) -- (k+2)/(n+2)
  ).cast
    (show γ _ = γ _ by
      congr 1
      simp
      have : (n : ℝ) + 1 > 0 := by
        rw [←Nat.cast_succ]
        exact Nat.cast_pos.mpr (Nat.succ_pos n)
      rw [←one_div, FractionEqualities.one_sub_inverse_of_add_one, FractionEqualities.frac_cancel', ← add_div]
      · linarith
      · linarith
    )
    rfl := by
  ext x
  show γ _ = γ _
  congr 1
  simp
  have : (n : ℝ) > 0 := Nat.cast_pos.mpr (lt_of_le_of_lt (Nat.zero_le k) hkn)
  -- Rewrite left side to ... / (n+1+1)
  rw [← one_div]
  rw [FractionEqualities.one_sub_inverse_of_add_one _]
  rw [FractionEqualities.one_sub_frac]
  rw [FractionEqualities.one_sub_frac]
  rw [mul_comm (((n : ℝ) - ↑k) / _) (x : ℝ)]
  rw [mul_div]
  rw [← add_div]
  rw [FractionEqualities.frac_cancel']
  rw [← add_div]
  -- Rewrite right side to ... / (n+1+1)
  rw [mul_comm _ (x : ℝ)]
  rw [mul_div]
  rw [← add_div]
  -- Show that numerators are equal
  congr 1
  ring
  repeat { linarith }

/-! ### Trans Parts -/

variable {x₂ : X}

/--
If `γ₁` and `γ₂` are two paths, then the first part of `γ₁.trans γ₂` split at `1/2` is `γ₁`
-/
lemma first_part_trans (γ₁ : Dipath x₀ x₁) (γ₂ : Dipath x₁ x₂) :
    (FirstPartDipath (γ₁.trans γ₂) (Fraction zero_lt_two one_le_two)) =
      γ₁.cast rfl (Dipath.trans_eval_at_half γ₁ γ₂) := by
  ext t
  rw [first_part_apply, Dipath.trans_apply]
  simp [t.2.2]
  rfl

/--
If `γ₁` and `γ₂` are two paths, then the second part of `γ₁.trans γ₂` split at `1/2` is `γ₂`
-/
lemma second_part_trans (γ₁ : Dipath x₀ x₁) (γ₂ : Dipath x₁ x₂) :
    (SecondPartDipath (γ₁.trans γ₂) (Fraction zero_lt_two one_le_two)) =
    γ₂.cast (Dipath.trans_eval_at_half γ₁ γ₂) rfl := by
  ext t
  rw [second_part_apply, Dipath.trans_apply]
  have h_two : 2 * (2⁻¹ : ℝ) = 1 := by norm_num
  have ht : 2 * (2⁻¹ * (t : ℝ) + 2⁻¹) - 1 = ↑t
  · rw [mul_add]
    rw [←mul_assoc]
    rw [h_two]
    ring
  have : (1 - 2⁻¹ : ℝ) = 2⁻¹ := by norm_num
  simp [this]
  by_cases h : 2⁻¹ * (t : ℝ) ≤ 0
  · have : t = 0 := Subtype.coe_inj.mp (show (t : ℝ) = 0 by linarith [t.2.1])
    simp [h, this]
    exact (Dipath.trans_eval_at_half _ _).symm
  · simp [h, ht]
    rfl

/--
If `γ₁` and `γ₂` are two paths, then the first part of `γ₁.trans γ₂` split at `1/(2n + 2)` is the
same as `γ₁` split at `1/(n + 1)`.
-/
lemma trans_first_part (γ₁: Dipath x₀ x₁) (γ₂ : Dipath x₁ x₂) (n : ℕ) (t : I) :
    (FirstPartDipath (γ₁.trans γ₂) (Fraction.ofPos (Nat.succ_pos (n + n).succ))) t =
      (FirstPartDipath γ₁ (Fraction.ofPos (Nat.succ_pos n))) t := by
  rw [first_part_apply]
  rw [first_part_apply]
  rw [Dipath.trans_apply]
  simp
  have : (n + n + 1 + 1 : ℝ) ≥ 2
  · rw [←Nat.cast_add]
    have : (↑(n + n) : ℝ) ≥ 0 := Nat.cast_nonneg (n + n)
    linarith

  have h₁ : (n + n + 1 + 1 : ℝ)⁻¹ ≤ 2⁻¹ := inv_le_inv_of_le zero_lt_two this
  have : (n + n + 1 + 1 : ℝ)⁻¹ * ↑t ≤ 2⁻¹
  · rw [← mul_one (2⁻¹ : ℝ)]
    apply mul_le_mul h₁ t.2.2 t.2.1
    norm_num
  rw [dif_pos this]
  apply congr_arg
  ext
  simp
  rw [←mul_assoc]
  congr 1
  have : (n + n + 1 + 1 : ℝ)  = (2 * (n + 1)) := by ring
  rw [this]
  rw [mul_inv]
  rw [←mul_assoc]
  norm_num

namespace AuxEqualities

lemma h₁ (t : I) : 0 ≤ (t : ℝ) := t.2.1
lemma h₂ (n : ℕ) : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
lemma h₃ (n : ℕ) : (n + 1 + 1 : ℝ) ≠ 0 := by linarith [h₂ n]
lemma h₄ (n : ℕ) : (↑n + ↑n + 1 + 1 + 1 + 1 : ℝ) > 0 := by linarith [h₂ n]
lemma h₅ (n : ℕ) : (↑n + ↑n + 1 + 1 + 1 + 1 : ℝ) = 2 * (↑n + 1 + 1) := by ring
lemma h₆ (n : ℕ) : (↑n + 1 + 1 : ℝ) / (↑n + ↑n + 1 + 1 + 1 + 1) = 2⁻¹ := by
  rw [h₅ n]
  rw [mul_comm]
  rw [div_mul_eq_div_div]
  rw [div_self (h₃ n)]
  exact one_div _
lemma h₇ (n : ℕ) : (n + n + 1 + 1 + 1: ℝ) ≠ 0 := by linarith [h₂ n]
lemma h₈ (n : ℕ) : (↑n + 1 + (↑n + 1) + 1 + 1 : ℝ) = (↑n + ↑n + 1 + 1 + 1 + 1) := by ring

lemma e₁ (n : ℕ) (t : I) :
    (1 - (n + 1 : ℝ) / (↑n + 1 + 1)) * ↑t + (↑n + 1) / (↑n + 1 + 1) =
    ((t : ℝ) + ↑n + 1) / (↑n + 1 + 1) := by
  nth_rewrite 1 [←div_self (h₃ n)]
  ring

lemma e₂ (n : ℕ) (t : I) :
    ((1 - (n + n + 1 + 1 : ℝ) / (↑n + ↑n + 1 + 1 + 1)) * ↑t + (↑n + ↑n + 1 + 1) / (↑n + ↑n + 1 + 1 + 1)) =
    (↑t + ↑n + ↑n + 1 + 1) / (↑n + ↑n + 1 + 1 + 1) := by
  nth_rewrite 1 [←div_self (h₇ n)]
  ring

lemma e₃ (n : ℕ) :
    (1 - (n + 1 + (n + 1) + 1 + 1 : ℝ)⁻¹) =
    (↑n + ↑n + 1 + 1 + 1) / (↑n + ↑n + 1 + 1 + 1 + 1) := by
  nth_rewrite 1 [←div_self (ne_of_gt (h₄ n))]
  ring_nf

lemma e₄ (n : ℕ) (t : I) :
    ((↑n + ↑n + 1 + 1 + 1 : ℝ) / (↑n + ↑n + 1 + 1 + 1 + 1) * ((↑t + ↑n + ↑n + 1 + 1) / (↑n + ↑n + 1 + 1 + 1))) =
    (↑t + ↑n + ↑n + 1 + 1) / (↑n + ↑n + 1 + 1 + 1 + 1) := by
  rw [mul_comm]
  rw [div_mul_div_cancel _ (h₇ n)]

lemma e₅ (n : ℕ) (r : ℝ) :
    2 * (r / (n + n + 1 + 1 + 1 + 1 : ℝ) + ((n : ℝ) + 1 + (↑n + 1) + 1 + 1)⁻¹) =
    (r + 1) / (↑n + 1 + 1) := by
  rw [h₈]
  rw [← one_div]
  rw [div_add_div_same]
  rw [h₅]
  rw [mul_div]
  rw [mul_comm]
  rw [← mul_div]
  rw [div_mul_eq_div_div]
  rw [div_self (show (2 : ℝ) ≠ 0 by norm_num)]
  ring

lemma e₆ (n : ℕ) (r : ℝ) :
  (1 - (n + 1 + 1 : ℝ)⁻¹) * r + (n + 1 + 1 : ℝ)⁻¹ = ((n + 1) * r + 1) / (n + 1 + 1) := by
  nth_rewrite 1 [←div_self (h₃ n)]
  ring

end AuxEqualities
open AuxEqualities

/--
If `γ₁` and `γ₂` are two paths, then
  `γ₁.trans γ₂` --> `[1/(2n + 4), 1]` --> `[0, (2n + 2)/(2n + 3)]` (so taking `[1/(2n + 4), (2n + 3)/(2n + 4)]`)
is the same as
  `γ₁` --> `[1/(n+2), 1]`, added to `γ₂` --> `[0, (n+1)/(n+2)]`
-/
lemma trans_first_part_of_second_part (γ₁: Dipath x₀ x₁) (γ₂ : Dipath x₁ x₂) (n : ℕ) (t : I) :
  (FirstPartDipath
    (SecondPartDipath (γ₁.trans γ₂) (Fraction.ofPos $ Nat.succ_pos (n.succ + n.succ).succ))
    (Fraction (Nat.succ_pos (n + n).succ.succ) (le_of_lt (Nat.lt_succ_self ((n + n).succ.succ))))
   ) t
  =
  ((SecondPartDipath γ₁ (Fraction.ofPos (Nat.succ_pos n.succ)))).trans
   (FirstPartDipath γ₂ (Fraction (Nat.succ_pos n.succ) (Nat.le_succ n.succ))) t := by
  rw [first_part_apply, second_part_apply, Dipath.trans_apply, Dipath.trans_apply]
  have : (n : ℝ) + ↑n + 2 + 1 = ↑n + ↑n + 1 + 1 + 1 := by ring
  split_ifs with h ht ht
  · rw [second_part_apply]
    apply congr_arg
    simp
    rw [e₃, mul_comm _ (t : ℝ), mul_div]
    rw [mul_comm (_/_) (_/_)]
    rw [this]
    rw [div_mul_div_cancel _ (h₇ n)]
    rw [e₆]
    rw [e₅]
    ring
  · exfalso
    revert h
    apply not_le.mpr
    simp
    rw [e₃]
    rw [mul_comm _ (t : ℝ)]
    rw [mul_div]
    rw [mul_comm (_/_) (_/_)]
    rw [this]
    rw [div_mul_div_cancel _ (h₇ n)]
    apply (mul_lt_mul_left (show 0 < (2 : ℝ) by norm_num)).mp
    rw [e₅]
    apply (lt_div_iff (show (n + 1 + 1 : ℝ) > 0 by linarith [h₂ n])).mpr
    norm_num
    push_neg at ht
    calc (n + 1 : ℝ)
      _ = 1 * (n + 1 : ℝ) := by rw [one_mul]
      _ = (2⁻¹ * 2) * (n + 1 : ℝ) := by rw [inv_mul_cancel (show (2 : ℝ) ≠ 0 by norm_num)]
      _ = 2⁻¹ * (n + n + 1 + 1 : ℝ) := by ring
      _ = 1/2 * (n + n + 1 + 1 : ℝ) := by rw [one_div]
      _ < t * (n + n + 1 + 1 : ℝ) := (mul_lt_mul_right (by linarith [h₂ n])).mpr ht
  · exfalso
    revert h
    apply imp_false.mpr
    apply not_not.mpr
    simp
    rw [e₃, mul_comm _ (t : ℝ), mul_div, mul_comm (_/_) (_/_)]
    rw [this]
    rw [div_mul_div_cancel _ (h₇ n)]
    apply (mul_le_mul_left (show 0 < (2 : ℝ) by norm_num)).mp
    rw [e₅]
    apply (div_le_iff (show (n + 1 + 1 : ℝ) > 0 by linarith [h₂ n])).mpr
    norm_num
    calc ↑t * (n + n + 1 + 1 : ℝ)
      _ ≤ 1/2 * (n + n + 1 + 1 : ℝ) := (mul_le_mul_right (by linarith [h₂ n])).mpr ht
      _ = (1/2 * 2) * (n + 1 : ℝ)   := by ring
      _ = 1 * (n + 1 : ℝ)           := by rw [div_mul_cancel (1 : ℝ) (show (2 : ℝ) ≠ 0 by norm_num)]
      _ = (n + 1 : ℝ)               := by rw [one_mul]
  · rw [first_part_apply]
    apply congr_arg
    simp
    rw [e₃]
    rw [mul_comm _ (t : ℝ)]
    rw [mul_div]
    rw [mul_comm (_/_) (_/_)]
    rw [this]
    rw [div_mul_div_cancel _ (h₇ n)]
    rw [e₅]
    nth_rewrite 6 [←div_self (h₃ n)]
    ring

/--
If `γ₁` and `γ₂` are two paths, then
  `γ₁.trans γ₂` --> `[1/(2n + 4), 1]` --> `[(2n+2)/(2n+3), 1]` (so to `[(2n+3)/(2n+4), 1]`)
is the same as
  `γ₂` --> `[(n+1)/(n+2), 1]`
-/
lemma trans_second_part_second_part (γ₁: Dipath x₀ x₁) (γ₂ : Dipath x₁ x₂) (n : ℕ) (t : I) :
  (SecondPartDipath
    (SecondPartDipath (γ₁.trans γ₂) $ Fraction.ofPos $ Nat.succ_pos (n.succ + n.succ).succ)
    (Fraction (Nat.succ_pos (n + n).succ.succ) (Nat.le_succ (n + n).succ.succ))
   ) t
  =
    (SecondPartDipath γ₂ (Fraction (Nat.succ_pos n.succ) (Nat.le_succ n.succ))) t := by
  rw [second_part_apply]
  rw [second_part_apply]
  rw [second_part_apply]
  rw [Dipath.trans_apply]
  simp
  have : (n : ℝ) + ↑n + 2 = ↑n + ↑n + 1 + 1 := by ring
  split_ifs with h
  · exfalso
    rw [this] at h
    rw [e₂] at h
    rw [e₃] at h
    rw [e₄] at h
    rw [←one_div] at h
    rw [h₈] at h
    rw [div_add_div_same] at h
    have : (↑n + 1 + 1 : ℝ) < (↑t + ↑n + ↑n + 1 + 1 + 1) := by linarith [h₂ n, h₁ t]
    have := lt_of_lt_of_le (div_lt_div_of_lt (h₄ n) this) h
    rw [h₆] at this
    exact lt_irrefl _ this
  apply congr_arg
  simp
  rw [this]
  rw [e₁, e₂, e₃, e₄, e₅]
  nth_rewrite 6 [←div_self (h₃ n)]
  rw [div_sub_div_same]
  ring

/--
If `γ₁` and `γ₂` are two paths, then `γ₁.trans γ₂` evaluated at `1/(2n+2)` is the same as
`γ₁` evaluated at `1/(n+1)`. -- TODO: Generalize
-/
lemma trans_image_inv_eq_first (γ₁: Dipath x₀ x₁) (γ₂ : Dipath x₁ x₂) (n : ℕ) :
    (γ₁.trans γ₂) (Fraction.ofPos (Nat.succ_pos (n + n).succ)) =
      γ₁ (Fraction.ofPos (Nat.succ_pos n)) := by
  have := trans_first_part γ₁ γ₂ n 1
  rw [SplitDipath.first_part_apply] at this
  rw [SplitDipath.first_part_apply] at this
  convert this using 2
  simp
  simp

/--
If `γ₁` and `γ₂` are two paths, then `γ₁.trans γ₂` --> `[1/(2n+4), 1]` evaluated at `(2n+2)/(2n+3)` is the same as
`γ₂` evaluated at `(n+1)/(n+2)`. -- TODO: Rename
-/
lemma second_part_trans_image_inv_eq_second (γ₁: Dipath x₀ x₁) (γ₂ : Dipath x₁ x₂) (n : ℕ) :
    (SecondPartDipath (γ₁.trans γ₂) $ Fraction.ofPos $ Nat.succ_pos (n.succ + n.succ).succ)
    (Fraction (Nat.succ_pos (n+n).succ.succ) (le_of_lt (Nat.lt_succ_self _)))
    = γ₂ (Fraction (Nat.succ_pos (n.succ)) (le_of_lt (Nat.lt_succ_self _))) := by
  rw [second_part_apply]
  rw [Dipath.trans_apply]
  have : (n : ℝ) + ↑n + 2 = ↑n + ↑n + 1 + 1 := by ring
  rw [dif_neg]
  · apply congr_arg
    simp
    rw [e₃]
    rw [mul_comm (_ / _) (_ / _)]
    rw [this]
    rw [div_mul_div_cancel _ (h₇ n)]
    rw [e₅ n (↑n + ↑n + 1 + 1)]
    nth_rewrite 6 [←div_self (h₃ n)]
    ring
  simp
  rw [e₃]
  rw [mul_comm]
  rw [this]
  rw [div_mul_div_cancel _ (h₇ n)]
  rw [h₈]
  rw [← one_div (n + n + 1 + 1 + 1 + 1 : ℝ)]
  rw [div_add_div_same]
  apply (lt_div_iff (h₄ n)).mpr
  rw [h₅]
  rw [←mul_assoc]
  norm_num
  linarith [h₂ n]

end SplitProperties

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

lemma first_part_cast {x₀' x₁' : X} (γ : Dipath x₀ x₁) (hx₀ : x₀' = x₀) (hx₁ : x₁' = x₁) (T : I) :
  (first_part_dipath (γ.cast hx₀ hx₁) T) = (first_part_dipath γ T).cast hx₀ rfl := rfl

lemma second_part_cast {x₀' x₁' : X} (γ : Dipath x₀ x₁) (hx₀ : x₀' = x₀) (hx₁ : x₁' = x₁) (T : I) :
  (second_part_dipath (γ.cast hx₀ hx₁) T) = (second_part_dipath γ T).cast rfl hx₁ := rfl

lemma first_part_eq_of_split_point_eq (γ : Dipath x₀ x₁) {T T' : I} (hT : T = T') :
  (first_part_dipath γ T) = (first_part_dipath γ T').cast rfl (congr_arg γ hT) := by subst_vars; rfl

lemma second_part_eq_of_split_point_eq (γ : Dipath x₀ x₁) {T T' : I} (hT : T = T') :
  (second_part_dipath γ T) = (second_part_dipath γ T').cast (congr_arg γ hT) rfl := by subst_vars; rfl

lemma first_part_eq_of_point_eq (γ : Dipath x₀ x₁) {T T': I} (h : T = T') (t : I) :
  (first_part_dipath γ T) t = (first_part_dipath γ T') t := by subst_vars; rfl

lemma second_part_eq_of_point_eq (γ : Dipath x₀ x₁) {T T': I} (h : T = T') (t : I) :
  (second_part_dipath γ T) t = (second_part_dipath γ T') t := by subst_vars; rfl


/-! ### First Part -/

-- TODO: Remove this note, NOTE: removed the 0 < T condition, so the proof will have to be altered
lemma first_part_image (γ : Dipath x₀ x₁) (T : I) (a b : I) :
    (first_part_dipath γ T) '' Icc a b = γ '' Icc (T * a) (T * b) := sorry

lemma first_part_range (γ : Dipath x₀ x₁) (T : I) :
    range (first_part_dipath γ T) = (γ '' Icc 0 T) := by
  rw [Dipath.range_eq_image_I _]
  convert first_part_image γ T 0 1 <;> norm_num

lemma first_part_range_interval (γ : Dipath x₀ x₁) {n : ℕ} (h : 0 < n) :
    range (first_part_dipath γ (Fraction.ofPos h)) = γ ''  Icc 0 (Fraction.ofPos h) :=
  first_part_range γ (Fraction.ofPos h)

lemma first_part_range_interval_coe (γ : Dipath x₀ x₁) {n : ℕ} (h : 0 < n):
    range (first_part_dipath γ (Fraction.ofPos h)) = γ.extend ''  Icc 0 (1/(↑n)) := by
  rw [first_part_range_interval γ h, ←Dipath.image_extend_eq_image, Fraction.ofPos_coe]
  rfl

/--
If `γ` is a path, then the image of `[i/(d+1), (i+1)/(d+1)]` under `γ` split at `(d+1)/(n+1)` is the
image of `[i/(n+1), (i+1)/(n+1)]` under `γ`
-/
lemma first_part_range_interval_partial (γ : Dipath x₀ x₁) {n d i : ℕ} (hd : d.succ < n.succ) (hi : i < d.succ) :
  (first_part_dipath γ (Fraction (Nat.succ_pos n) (le_of_lt hd))) '' Icc -- First part at (d + 1)/(n + 1)
    (Fraction (Nat.succ_pos d) (le_of_lt hi)) -- frac i/(d+1)
    (Fraction (Nat.succ_pos d) (Nat.succ_le_of_lt hi)) -- frac (i+1)/(d+1)
    = γ ''  Icc
    (Fraction (Nat.succ_pos n) (le_of_lt (lt_trans hi hd))) -- frac i/(n+1)
    (Fraction (Nat.succ_pos n) (Nat.succ_le_of_lt (lt_trans hi hd))) -- frac (i+1)/(n+1)
  := by
  convert first_part_image γ (Fraction (Nat.succ_pos n) (le_of_lt hd))
    (Fraction (Nat.succ_pos d) (le_of_lt hi)) (Fraction (Nat.succ_pos d) (Nat.succ_le_of_lt hi)) <;>
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
lemma first_part_range_interval_partial_coe (γ : Dipath x₀ x₁) {n d i : ℕ} (hd : d.succ < n.succ) (hi : i < d.succ) :
    (first_part_dipath γ (Fraction (Nat.succ_pos n) (le_of_lt hd))).extend '' Icc (↑i/(↑d+1)) ((↑i+1)/(↑d+1))
      = γ.extend ''  Icc (↑i/(↑n+1)) ((↑i+1)/(↑n+1)) := by
  have := first_part_range_interval_partial γ hd hi
  rw [←Dipath.image_extend_eq_image] at this
  rw [←Dipath.image_extend_eq_image] at this
  convert this <;> exact (Nat.cast_succ _).symm

/-! ### Second Part -/

-- TODO: Remove this note, NOTE: removed the T < 1 condition, so the proof will have to be altered
lemma second_part_image (γ : Dipath x₀ x₁) (T : I) (a b : I) :
  (second_part_dipath γ hT) '' Icc a b = γ '' Icc
    ⟨σ T * a + T, interp_left_mem_I T a⟩
    ⟨σ T * b + T, interp_left_mem_I T b⟩ := sorry

lemma second_part_range (γ : Dipath x₀ x₁) (T : I) :
    range (second_part_dipath γ T) = γ '' Icc T 1  := by
  rw [Dipath.range_eq_image_I _]
  convert second_part_image γ T 0 1 using 3 <;> simp

/--
  When γ is a dipath, an we split it on the intervals [0, 1/(n+1)] and [1/(n+1), 1], then the image of γ of
  [(i+1)/(n+1), (i+2)/(n+1)] is equal to the image the second part of γ of [i/n, (i+1)/n]
-/
lemma second_part_range_interval (γ : Dipath x₀ x₁) {i n : ℕ} (hi : i < n) (hn : 0 < n):
    (second_part_dipath γ (Fraction.ofPos (Nat.succ_pos n))) '' Icc
      (Fraction hn (le_of_lt hi)) (Fraction hn (Nat.succ_le_of_lt hi)) =
    γ ''  Icc (Fraction (Nat.succ_pos n) (show i+1 ≤ n+1 by exact (le_of_lt (Nat.succ_lt_succ hi))))
              (Fraction (Nat.succ_pos n) (show i+2 ≤ n+1 by exact Nat.succ_lt_succ (Nat.succ_le_of_lt hi))) := sorry

/--
  When γ is a dipath, an we split it on the intervals [0, 1/(n+1)] and [1/(n+1), 1], then the image of γ of
  [(i+1)/(n+1), (i+2)/(n+1)] is equal to the image the second part of γ of [i/n, (i+1)/n].
  Version with interval of real numbers
-/
lemma second_part_range_interval_coe (γ : Dipath x₀ x₁) {i n : ℕ} (hi : i < n) (hn : 0 < n):
    (second_part_dipath γ (Fraction.ofPos (Nat.succ_pos n))).extend '' Icc (↑i/↑n) ((↑i+1)/↑n) =
    γ.extend ''  Icc ((↑i+1)/(↑n+1)) ((↑i+1+1)/(↑n+1)) := sorry

/--
  When γ is a dipath, an we split it on the intervals [0, (d+1)/(n+1)] and [(d+1)/(n+1), 1], then the image of γ of
  [(i+d.succ)/(n+1), (i+d.succ+1)/(n+1)] is equal to the image the second part of γ of [(i/(n-d), (i+1)/(n-d)].
-/
lemma second_part_range_partial_interval (γ : Dipath x₀ x₁) {i d n : ℕ} (hd : d.succ < n.succ) (hi : i < n - d) :
    (second_part_dipath γ (Fraction (Nat.succ_pos n) hd)) '' Icc
      (Fraction (Nat.sub_pos_of_lt (Nat.lt_of_succ_lt_succ hd)) (le_of_lt hi)) -- i/(n-d)
      (Fraction (Nat.sub_pos_of_lt (Nat.lt_of_succ_lt_succ hd)) (Nat.succ_le_of_lt hi)) -- (i+1)/(n-d)
      := sorry

/--
  When γ is a dipath, an we split it on the intervals [0, (d+1)/(n+1)] and [(d+1)/(n+1), 1], then the image of γ of
  [(i+d.succ)/(n+1), (i+d.succ+1)/(n+1)] is equal to the image the second part of γ of [(i/(n-d), (i+1)/(n-d)].
-/
lemma second_part_range_partial_interval_coe (γ : Dipath x₀ x₁) {i d n : ℕ} (hd : d.succ < n.succ) (hi : i < n - d) :
  (second_part_dipath γ (Fraction (Nat.succ_pos n) (le_of_lt hd))).extend '' Icc (↑i/(↑n-↑d)) ((↑i+1)/(↑n-↑d))
    = γ.extend ''  Icc ((↑(i+d.succ))/(↑n+1)) ((↑(i+d.succ) + 1)/(↑n+1)) := sorry

/-! ### Mixed Parts -/

/-
  Splitting a dipath at k/n and then at 1/k is the same as splitting it at 1/n
-/
lemma first_part_of_first_part (γ : Dipath x₀ x₁) {n k : ℕ} (hkn : k < n) (hk : 0 < k) :
  first_part_dipath
    (first_part_dipath γ (Fraction (lt_trans hk hkn) (le_of_lt hkn))) -- k/n
    (Fraction.ofPos hk) -- 1/k
  = (first_part_dipath γ (Fraction.ofPos $ lt_trans hk hkn)).cast rfl
    (show γ _ = γ _ by { congr 1; rw [←Fraction.mul_inv hk (le_of_lt hkn)]; rfl }) -- 1/n
:= sorry

/--
  Splitting a dipath [0, (k+1)/(n+1)] and then [1/(k+1), 1] is the same as splitting it [1/(n+1), 1] and then [0, k/n]
-/
lemma first_part_of_second_part (γ : Dipath x₀ x₁) {n k : ℕ} (hkn : k < n) (hk : 0 < k) :
  second_part_dipath
    (first_part_dipath γ (Fraction (Nat.succ_pos n) (le_of_lt $ Nat.succ_lt_succ hkn))) -- (k+1)/(n+1)
    (Fraction.ofPos (Nat.succ_pos k)) -- 1/(k+1)
  =
  (first_part_dipath
      (second_part_dipath γ (Fraction.ofPos (Nat.succ_pos n))) -- 1/(n+1)
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
    := sorry

/--
  Splitting a dipath [(k+2)/(n+2), 1] is the same as splitting it [1/(n+2), 1] and then [(k+1)/(n+1), 1]
-/
lemma second_part_of_second_part (γ : Dipath x₀ x₁) {n k : ℕ} (hkn : k < n) :
  second_part_dipath
    (second_part_dipath γ (Fraction.ofPos (Nat.succ_pos n.succ))) -- 1/(n+2)
    (Fraction (Nat.succ_pos n) (Nat.succ_lt_succ hkn)) -- (k+1)/(n+1)
  =
  (
    second_part_dipath γ (Fraction (Nat.succ_pos n.succ) (Nat.succ_lt_succ (Nat.succ_lt_succ hkn))) -- (k+2)/(n+2)
  ).cast
    (show γ _ = γ _ by
      congr 1
      simp
      have : (n : ℝ) + 1 > 0 := by
        rw [←Nat.cast_succ]
        exact Nat.cast_pos.mpr (Nat.succ_pos n)
      rw [←one_div, FractionEqualities.one_sub_inverse_of_add_one, FractionEqualities.frac_cancel', ← add_div]
      · ring
      · linarith
      · linarith
    )
    rfl := sorry

/-! ### Trans Parts -/

variable {x₂ : X}

/--
If `γ₁` and `γ₂` are two paths, then the first part of `γ₁.trans γ₂` split at `1/2` is `γ₁`
-/
lemma first_part_trans (γ₁ : Dipath x₀ x₁) (γ₂ : Dipath x₁ x₂) :
  (first_part_dipath (γ₁.trans γ₂) (Fraction zero_lt_two one_le_two)) = γ₁.cast rfl (Dipath.trans_eval_at_half γ₁ γ₂) := sorry

/--
If `γ₁` and `γ₂` are two paths, then the second part of `γ₁.trans γ₂` split at `1/2` is `γ₂`
-/
lemma second_part_trans (γ₁ : Dipath x₀ x₁) (γ₂ : Dipath x₁ x₂) :
  (second_part_dipath (γ₁.trans γ₂) (Fraction zero_lt_two one_le_two)) = γ₂.cast (Dipath.trans_eval_at_half γ₁ γ₂) rfl := sorry

/--
If `γ₁` and `γ₂` are two paths, then the first part of `γ₁.trans γ₂` split at `1/(2n + 2)` is the
same as `γ₁` split at `1/(n + 1)`.
-/
lemma trans_first_part (γ₁: Dipath x₀ x₁) (γ₂ : Dipath x₁ x₂) (n : ℕ) (t : I) :
  (first_part_dipath (γ₁.trans γ₂) (Fraction.ofPos (Nat.succ_pos (n + n).succ))) t =
    (first_part_dipath γ₁ (Fraction.ofPos (Nat.succ_pos n))) t := sorry

/--
If `γ₁` and `γ₂` are two paths, then
  `γ₁.trans γ₂` --> `[1/(2n + 4), 1]` --> `[0, (2n + 2)/(2n + 3)]` (so taking `[1/(2n + 4), (2n + 3)/(2n + 4)]`)
is the same as
  `γ₁` --> `[1/(n+2), 1]`, added to `γ₂` --> `[0, (n+1)/(n+2)]`
-/
lemma trans_first_part_of_second_part (γ₁: Dipath x₀ x₁) (γ₂ : Dipath x₁ x₂) (n : ℕ) (t : I) :
  (first_part_dipath
    (second_part_dipath (γ₁.trans γ₂) (Fraction.ofPos $ Nat.succ_pos (n.succ + n.succ).succ))
    (Fraction (Nat.succ_pos (n.succ + n.succ)) $ le_of_lt $ Nat.lt_succ_self (n.succ + n.succ))
   ) t
  =
  ((second_part_dipath γ₁ (Fraction.ofPos (Nat.succ_pos n.succ)))).trans
   (first_part_dipath γ₂ (Fraction (Nat.succ_pos n.succ) (Nat.le_succ n.succ))) t := sorry

/--
If `γ₁` and `γ₂` are two paths, then
  `γ₁.trans γ₂` --> `[1/(2n + 4), 1]` --> `[(2n+2)/(2n+3), 1]` (so to `[(2n+3)/(2n+4), 1]`)
is the same as
  `γ₂` --> `[(n+1)/(n+2), 1]`
-/
lemma trans_second_part_second_part (γ₁: Dipath x₀ x₁) (γ₂ : Dipath x₁ x₂) (n : ℕ) (t : I) :
  (second_part_dipath
    (second_part_dipath (γ₁.trans γ₂) $ Fraction.ofPos $ Nat.succ_pos (n.succ + n.succ).succ)
    (Fraction (Nat.succ_pos (n + n).succ.succ) (Nat.le_succ (n + n).succ.succ))
   ) t
  =
    (second_part_dipath γ₂ (Fraction (Nat.succ_pos n.succ) (Nat.le_succ n.succ))) t := sorry

/--
If `γ₁` and `γ₂` are two paths, then `γ₁.trans γ₂` evaluated at `1/(2n+2)` is the same as
`γ₁` evaluated at `1/(n+1)`. -- TODO: Generalize
-/
lemma trans_image_inv_eq_first (γ₁: Dipath x₀ x₁) (γ₂ : Dipath x₁ x₂) (n : ℕ) :
  (γ₁.trans γ₂) (Fraction.ofPos (Nat.succ_pos (n + n).succ)) = γ₁ (Fraction.ofPos (Nat.succ_pos n)) := sorry

/--
If `γ₁` and `γ₂` are two paths, then `γ₁.trans γ₂` --> `[1/(2n+4), 1]` evaluated at `(2n+2)/(2n+3)` is the same as
`γ₂` evaluated at `(n+1)/(n+2)`. -- TODO: Rename
-/
lemma second_part_trans_image_inv_eq_second (γ₁: Dipath x₀ x₁) (γ₂ : Dipath x₁ x₂) (n : ℕ) :
  (second_part_dipath (γ₁.trans γ₂) $ Fraction.ofPos $ Nat.succ_pos (n.succ + n.succ).succ)
    (Fraction (Nat.succ_pos (n+n).succ.succ) (le_of_lt (Nat.lt_succ_self _)))
   = γ₂ (Fraction (Nat.succ_pos (n.succ)) (le_of_lt (Nat.lt_succ_self _))) := sorry


end SplitProperties

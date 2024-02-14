import Lean4.cover_lemma
import Lean4.dipath_subtype
import Lean4.SplitPath.split_properties

/-
  This file contains the definition of a directed path being n-covered by two subspaces X₁ and X₂:
  It maps any subinterval [i/n, (i+1)/n] into either X₁ or X₂.
  We give this definition inductively.
  This file contains properties about dipaths and parts of dipaths being n-covered.
-/

open Set
open scoped unitInterval

noncomputable section

namespace Dipath

variable {X : dTopCat} {X₀ X₁ : Set X}

def covered {x₀ x₁ : X} (_ : X₀ ∪ X₁ = univ) (γ : Dipath x₀ x₁) : Prop :=
  (range γ ⊆ X₀) ∨ (range γ ⊆ X₁)

namespace covered

variable {x₀ x₁ : X}

lemma covered_refl (x : X) (hX : X₀ ∪ X₁ = univ) : covered hX (Dipath.refl x) := by
  cases ((Set.mem_union x X₀ X₁).mp (Filter.mem_top.mpr hX x))
  case inl hx₀ => left; exact DiSubtype.range_refl_subset_of_mem hx₀
  case inr hx₁ => right; exact DiSubtype.range_refl_subset_of_mem hx₁

lemma covered_of_extended_image_subset (γ : Dipath x₀ x₁) (hX : X₀ ∪ X₁ = univ) (hγ : γ.extend '' I ⊆ X₀ ∨ γ.extend '' I ⊆ X₁) :
    covered hX γ := by
  rw [(Dipath.range_eq_image γ).symm] at hγ
  exact hγ

lemma covered_of_covered_trans {x₂ : X} {γ₁: Dipath x₀ x₁} {γ₂ : Dipath x₁ x₂}
  {hX : X₀ ∪ X₁ = univ} (hγ : covered hX (γ₁.trans γ₂)):
    (covered hX γ₁ ∧ covered hX γ₂) := by
  unfold covered at *
  rw [Dipath.trans_range _ _] at hγ
  cases hγ
  case inl h =>
    constructor
    · exact Or.inl $ subset_trans (subset_union_left (range γ₁) (range γ₂)) h
    · exact Or.inl $ subset_trans (subset_union_right (range γ₁) (range γ₂)) h
  case inr h =>
    constructor
    · exact Or.inr $ subset_trans (subset_union_left (range γ₁) (range γ₂)) h
    · exact Or.inr $ subset_trans (subset_union_right (range γ₁) (range γ₂)) h

lemma covered_subparam_of_covered {γ : Dipath x₀ x₁} {hX : X₀ ∪ X₁ = univ} (hγ : covered hX γ) (f : D(I, I)) :
    covered hX (γ.subparam f) := by
  cases hγ
  case inl hγ =>
    exact Or.inl (subset_trans (Dipath.subparam_range γ f) hγ)
  case inr hγ =>
    exact Or.inr (subset_trans (Dipath.subparam_range γ f) hγ)

lemma covered_reparam_iff (γ : Dipath x₀ x₁) (hX : X₀ ∪ X₁ = univ) (f : D(I, I)) (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
    covered hX γ ↔ covered hX (γ.reparam f hf₀ hf₁) := by
  unfold covered
  rw [Dipath.range_reparam _ _]

lemma covered_cast_iff {x₀' x₁' : X}  (γ : Dipath x₀ x₁) (hX : X₀ ∪ X₁ = univ) (hx₀ : x₀' = x₀) (hx₁ : x₁' = x₁) :
    covered hX γ ↔ covered hX (γ.cast hx₀ hx₁) := by rfl

/--
 If γ is a dipath that is covered, then by splitting it into two parts [0, T] and [T, 1], both parts remain covered
-/
lemma covered_split_path {γ : Dipath x₀ x₁} {hX : X₀ ∪ X₁ = Set.univ} {T : I} (hT₀ : 0 < T) (hT₁ : T < 1) (hγ : covered hX γ):
    covered hX (SplitDipath.FirstPartDipath γ T) ∧ covered hX (SplitDipath.SecondPartDipath γ T) := by
  apply covered_of_covered_trans
  apply (covered_reparam_iff _ hX (SplitDipath.trans_reparam_map hT₀ hT₁) _ _).mpr
  rw [SplitDipath.first_trans_second_reparam_eq_self γ hT₀ hT₁] at hγ
  exact hγ

end covered

open covered

/--
We say that `covered_partwise hX γ n` if a dipath γ can be split into n+1 parts, each of which is covered by `X₁` or `X₂`
-/
def covered_partwise (hX : X₀ ∪ X₁ = Set.univ) {x y : X} (γ : Dipath x y) (n : ℕ) : Prop :=
  match n with
  | Nat.zero => covered hX γ
  | Nat.succ n => covered hX (SplitDipath.FirstPartDipath γ (Fraction.ofPos (show 0 < (n.succ + 1) by norm_num))) ∧
      covered_partwise hX (SplitDipath.SecondPartDipath γ (Fraction.ofPos (show 0 < (n.succ + 1) by norm_num))) n

namespace covered_partwise

lemma covered_partwise_of_equal (hX : X₀ ∪ X₁ = Set.univ) {x₀ x₁ : X} {γ₁ γ₂ : Dipath x₀ x₁} {n m : ℕ} (h : γ₁ = γ₂) (h' : n = m) (hγ₁ : covered_partwise hX γ₁ n) :
  covered_partwise hX γ₂ m := by subst_vars; exact hγ₁

/--
 If γ is a dipath that is fully covered, then it is also partwise covered for all n ∈ ℕ
-/
lemma covered_partwise_of_covered {hX : X₀ ∪ X₁ = Set.univ} (n : ℕ) :
    ∀ {x₀ x₁ : X} {γ : Dipath x₀ x₁}, covered hX γ → covered_partwise hX γ n := by
  induction n

  case zero =>
    intros _ _ _ hγ
    exact hγ

  case succ n ih =>
    intros x₀ x₁ γ hγ
    constructor
    · exact (covered_split_path (Fraction.ofPos_pos _) (Fraction.ofPos_lt_one (by norm_num)) hγ).left
    · apply ih
      exact (covered_split_path (Fraction.ofPos_pos _) (Fraction.ofPos_lt_one (by norm_num)) hγ).right

lemma covered_partwise_cast_iff  (hX : X₀ ∪ X₁ = univ) {n : ℕ} :
    ∀ {x₀ x₁ x₀' x₁' : X} (γ : Dipath x₀ x₁) (hx₀ : x₀' = x₀) (hx₁ : x₁' = x₁),
    covered_partwise hX γ n ↔ covered_partwise hX (γ.cast hx₀ hx₁) n := by
  induction n

  case zero =>
    intros x₀ x₁ x₀' x₁' γ hx₀ hx₁
    exact covered_cast_iff _ _ _ _

  case succ n ih =>
    intros x₀ x₁ x₀' x₁' γ hx₀ hx₁
    unfold covered_partwise
    rw [SplitProperties.firstPart_cast, SplitProperties.secondPart_cast]
    constructor
    · rintro ⟨hγ₁, hγ₂⟩
      constructor
      · exact (covered_cast_iff _ _ _ _).mp hγ₁
      · exact (ih _ _ _).mp hγ₂
    · rintro ⟨hγ₁, hγ₂⟩
      constructor
      · exact (covered_cast_iff _ _ _ _).mpr hγ₁
      · exact (ih _ _ _).mpr hγ₂

/--
 A dipath γ that can be covered with n+1 intervals can satisfied `covered_partwise _ γ n`.
 This is the converse of `covered_by_intervals_of_covered_partwise`.
-/
lemma covered_partwise_of_covered_by_intervals {hX : X₀ ∪ X₁ = Set.univ} (n : ℕ) :
    ∀ {x₀ x₁ : X} {γ : Dipath x₀ x₁}, (∀ (i : ℕ) (h : i < (n+1)),
      γ.extend '' Set.Icc ((↑i)/(↑n+1)) ((↑i+1)/(↑n+1)) ⊆ X₀ ∨
      γ.extend '' Set.Icc ((↑i)/(↑n+1)) ((↑i+1)/(↑n+1)) ⊆ X₁) → covered_partwise hX γ n := by
  induction n
  case zero =>
    intros x₀ x₁ γ hγ
    have := hγ 0 (by linarith)
    unfold covered_partwise covered
    rw [Dipath.range_eq_image]
    convert this <;> simp

  case succ n ih =>
    intros x₀ x₁ γ hγ
    constructor
    · unfold covered
      rw [SplitProperties.firstPart_range_interval γ _, ←Dipath.image_extend_eq_image]
      convert hγ 0 (by norm_num) <;> norm_num
    · apply ih
      intros i hi
      have : i + 1 < n + 2 := by linarith
      have h := hγ (i+1) (this)
      suffices :
        (SplitDipath.SecondPartDipath γ _).extend '' Set.Icc (↑i/(↑(n+1))) ((↑i+1)/(↑(n+1))) ⊆ X₀ ∨
        (SplitDipath.SecondPartDipath γ _).extend '' Set.Icc (↑i/(↑(n+1))) ((↑i+1)/(↑(n+1))) ⊆ X₁
      · convert this <;> exact (Nat.cast_succ n).symm

      rw [SplitProperties.secondPart_range_interval_coe γ _ _]
      convert h <;> exact (Nat.cast_succ i).symm
      · exact hi
      · exact Nat.succ_pos n


/--
 A dipath γ that satisfies `covered_partwise _ γ n` can be covered with n+1 intervals.
 This is the converse of `covered_partwise_of_covered_by_intervals`.
-/
lemma covered_by_intervals_of_covered_partwise {hX : X₀ ∪ X₁ = Set.univ} (n : ℕ) :
    ∀ {x₀ x₁ : X} {γ : Dipath x₀ x₁}, covered_partwise hX γ n → (∀ (i : ℕ) (h : i < (n+1)),
      γ.extend '' Set.Icc ((↑i)/(↑n+1)) ((↑i+1)/(↑n+1)) ⊆ X₀ ∨
      γ.extend '' Set.Icc ((↑i)/(↑n+1)) ((↑i+1)/(↑n+1)) ⊆ X₁) := by
  induction n
  case zero =>
    intros x₀ x₁ γ hγ i hi
    rw [show i = 0 by linarith]
    suffices : γ.extend '' I ⊆ X₀ ∨ γ.extend '' I ⊆ X₁
    · convert this <;> simp
    rw [←Dipath.range_eq_image γ]
    exact hγ

  case succ n ih =>
    intros x₀ x₁ γ hγ i hi
    by_cases h_i_eq_0 : i = 0
    · have hγ_first_cov := hγ.left
      rw [h_i_eq_0]
      have := SplitProperties.firstPart_range_interval_coe γ (show 0 < n+2 by linarith)
      unfold covered at hγ_first_cov
      rw [this] at hγ_first_cov
      convert hγ_first_cov <;> simp
      ring
      ring
    · suffices : γ.extend '' Icc ((↑(i-1) + 1)/(↑(n.succ) + 1)) ((↑(i-1) + 1 + 1)/(↑(n.succ) + 1)) ⊆ X₀ ∨
              γ.extend '' Icc ((↑(i-1) + 1)/(↑(n.succ) + 1)) ((↑(i-1) + 1 + 1)/(↑(n.succ) + 1)) ⊆ X₁
      · convert this <;> rw [Nat.cast_sub (Nat.pos_of_ne_zero h_i_eq_0)] <;> simp

      have : i - 1 < n.succ := Nat.lt_of_succ_lt_succ ((Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero h_i_eq_0)).symm ▸ hi)
      rw [←SplitProperties.secondPart_range_interval_coe γ (this) (by linarith)]
      convert ih hγ.right (i-1) (this) <;> exact (Nat.cast_succ n)

/--
  Let γ be a dipath covered by n+1 parts. Let 0 < k < n+1 be given. Then the first part
  of γ, split by k/(n+1) is covered by k parts.
  Here, k = d.succ, so we don't need the requirement k > 0.
-/
lemma covered_partwise_first_part_d (hX : X₀ ∪ X₁ = Set.univ) {n d : ℕ} (hd_n : d.succ < n.succ) :
    ∀ {x₀ x₁ : X} {γ : Dipath x₀ x₁} (_ : covered_partwise hX γ n),
      covered_partwise hX (SplitDipath.FirstPartDipath γ $ Fraction (Nat.succ_pos n) (le_of_lt hd_n)) d := by
  intro x y γ hγ
  apply covered_partwise_of_covered_by_intervals
  intro i hi
  rw [SplitProperties.firstPart_range_interval_partial_coe γ hd_n hi]
  exact covered_by_intervals_of_covered_partwise n hγ i (lt_trans hi hd_n)

/--
  Input: (d+1) < (n+1) --> split at (d+1)/(n+1)
  Let γ be a dipath covered by n+1 parts. Let 0 < k < n+1 be given. Then the second part
  of γ, split by k/(n+1) is covered by n+1-k parts.
  Here, k = d.succ, so we don't need the requirement k > 0.
-/
lemma covered_partwise_second_part_d (hX : X₀ ∪ X₁ = Set.univ) {n d : ℕ} (hd_n : d.succ < n.succ) :
    ∀ {x₀ x₁ : X} {γ : Dipath x₀ x₁} (_ : covered_partwise hX γ n),
    covered_partwise hX (SplitDipath.SecondPartDipath γ $ Fraction (Nat.succ_pos n) (le_of_lt hd_n)) (n - d.succ) := by
  intros x y γ hγ
  apply covered_partwise_of_covered_by_intervals
  intros i hi
  rw [←Nat.cast_succ]
  have hi_lt_n_sub_d : i < n - d := by
    convert hi using 1
    rw [Nat.sub_succ]
    exact (Nat.succ_pred_eq_of_pos (Nat.sub_pos_of_lt (Nat.lt_of_succ_lt_succ hd_n))).symm
  have : i + d.succ < n + 1 := by
    rw [Nat.add_succ]
    apply Nat.succ_lt_succ
    exact lt_tsub_iff_right.mp hi_lt_n_sub_d
  have := covered_by_intervals_of_covered_partwise n hγ (i + d.succ) this
  rw [←SplitProperties.secondPart_range_partial_interval_coe γ hd_n hi_lt_n_sub_d] at this
  have h : (n-d.succ).succ = n - d := by
    rw [Nat.sub_succ]
    exact Nat.succ_pred_eq_of_pos (Nat.sub_pos_of_lt (Nat.lt_of_succ_lt_succ hd_n))
  convert this <;> rw [h] <;> exact Nat.cast_sub (le_of_lt $ Nat.lt_of_succ_lt_succ hd_n)

/--
  Let γ be a dipath covered by n+2 parts. Then the first part of γ, split by (n+1)/(n+2) is covered by n+1 parts.
-/
lemma covered_partwise_first_part_end_split (hX : X₀ ∪ X₁ = Set.univ) {n : ℕ} {x₀ x₁ : X}
  {γ : Dipath x₀ x₁} (hγ : covered_partwise hX γ n.succ) :
    covered_partwise hX (SplitDipath.FirstPartDipath γ $ Fraction (Nat.succ_pos n.succ) (Nat.le_succ n.succ)) n :=
  covered_partwise_first_part_d hX (Nat.lt_succ_self _) hγ

/--
  Let γ be a dipath covered by n+2 parts. Then the second part of γ, split by (n+1)/(n+2) is covered
-/
lemma covered_second_part_end_split (hX : X₀ ∪ X₁ = Set.univ) {n : ℕ} {x₀ x₁ : X}
  {γ : Dipath x₀ x₁} (hγ : covered_partwise hX γ n.succ) :
    covered hX (SplitDipath.SecondPartDipath γ $ Fraction (Nat.succ_pos n.succ) (Nat.le_succ n.succ)) := by
  have := covered_partwise_second_part_d hX (Nat.lt_succ_self n.succ) hγ
  rw [Nat.sub_self n.succ] at this
  exact this

/--
  Let γ be a dipath and n ≥ 2:
  If the first part [0, 1/(n+1)] can be covered with k intervals and the second part [1/(n+1), 1] can be covered with k*n intervals,
  then the entire path can be covered with k*(n+1) intervals.
-/
lemma covered_partwise_of_parts (hX : X₀ ∪ X₁ = Set.univ) {n : ℕ} (hn : 0 < n) {k : ℕ} (hk : k > 0) :
  Π {x₀ x₁ : X} {γ : Dipath x₀ x₁},
    ((covered_partwise hX (SplitDipath.FirstPartDipath γ (Fraction.ofPos (Nat.succ_pos n))) (k - 1)) ∧
    (covered_partwise hX (SplitDipath.SecondPartDipath γ (Fraction.ofPos (Nat.succ_pos n))) (n * k - 1))) →
    (covered_partwise hX γ ((n + 1) * k - 1)) := by
  rintro x₀ x₁ γ ⟨hγ_first, hγ_second⟩
  apply covered_partwise_of_covered_by_intervals
  intros i hi
  have prod_pos : (n + 1) * k > 0 := mul_pos (Nat.succ_pos n) hk
  set d' := k - 1 with d_def
  set n' := (n + 1) * k - 1 with n_def
  have hd_eq_k : d'.succ = k := by rw [d_def, ←Nat.pred_eq_sub_one k, Nat.succ_pred_eq_of_pos hk]
  have h₁ : d'.succ < n'.succ := by
    rw [n_def, hd_eq_k, ←Nat.pred_eq_sub_one ((n + 1) * k), Nat.succ_pred_eq_of_pos prod_pos]
    nth_rewrite 1 [←one_mul k]
    exact (mul_lt_mul_right hk).mpr (by linarith)

  have : Fraction (Nat.succ_pos n') (le_of_lt h₁) = Fraction.ofPos (Nat.succ_pos n) := by
    simp [d_def, n_def]
    rw [←Nat.cast_succ, ←Nat.cast_succ, ←Nat.pred_eq_sub_one k, Nat.succ_pred_eq_of_pos hk]
    rw [←Nat.pred_eq_sub_one ((n + 1) * k), Nat.succ_pred_eq_of_pos prod_pos, mul_comm, Nat.cast_mul]
    have : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hk)
    rw [←div_div, div_self this, Nat.cast_succ]
    exact one_div _

  have h₃ : (n' : ℝ) - (d' : ℝ) = (↑(n * k - 1) : ℝ) + 1 := by
    rw [←Nat.cast_sub (le_of_lt $ Nat.lt_of_succ_lt_succ h₁), ←Nat.cast_succ, ← Nat.pred_eq_sub_one (n * k)]
    rw [Nat.succ_pred_eq_of_pos (Nat.mul_pos hn hk), n_def, d_def, Nat.sub_sub, add_comm 1 (k-1)]
    rw [Nat.add_one (k-1), Nat.sub_one k, Nat.succ_pred_eq_of_pos hk, add_mul, one_mul]
    rw [Nat.add_sub_assoc (le_refl k), Nat.sub_self]
    rfl

  by_cases h : i < k
  · -- Use the covering of the first part of γ
    have h₂ : i < d'.succ := by
      rw [d_def, ←Nat.pred_eq_sub_one k, Nat.succ_pred_eq_of_pos hk]
      exact h
    rw [←SplitProperties.firstPart_range_interval_partial_coe γ h₁ h₂]
    convert (covered_by_intervals_of_covered_partwise (k-1) hγ_first i (by linarith))
  · push_neg at h
    set i' := i - d'.succ with i_def
    have h₂ : i' < n' - d' := by
      rw [i_def, ←Nat.succ_sub_succ n' d']
      have : d'.succ ≤ i := hd_eq_k.symm ▸ h
      apply (tsub_lt_tsub_iff_right this).mpr _
      exact hi
    have : i = i' + d'.succ := by
      rw [i_def, Nat.sub_add_cancel]
      exact hd_eq_k.symm ▸ h
    rw [this]
    have : i - k < n * k - 1 + 1 := by
      rw [Nat.sub_one (n * k), Nat.add_one (n * k).pred, Nat.succ_pred_eq_of_pos (mul_pos hn hk)]
      apply (tsub_lt_iff_right h).mpr _
      nth_rewrite 2 [←one_mul k]
      rw [←add_mul, ←Nat.succ_pred_eq_of_pos prod_pos]
      convert hi using 1

    rw [←SplitProperties.secondPart_range_partial_interval_coe γ h₁ h₂]
    convert (covered_by_intervals_of_covered_partwise (n * k - 1) hγ_second (i - k) this)

/--
  If a dipath γ can be covered in n+1 parts, it can also be covered in (k+1) * (n+1) parts
-/
lemma covered_partwise_refine (hX : X₀ ∪ X₁ = Set.univ) (n k : ℕ) :
    Π {x₀ x₁ : X} {γ : Dipath x₀ x₁}, covered_partwise hX γ n → covered_partwise hX  γ ((n + 1) * (k + 1) - 1) := by
  induction n
  case zero =>
    intros x₀ x₁ γ hγ
    exact covered_partwise_of_covered ((0+1)*(k+1)-1) hγ

  case succ n ih =>
    rintro x₀ x₁ γ ⟨hγ_cov_first, hγ_split_cov_second⟩
    apply covered_partwise_of_parts hX (Nat.succ_pos n) (Nat.succ_pos k)
    constructor
    · exact covered_partwise_of_covered k hγ_cov_first
    · convert ih hγ_split_cov_second

lemma covered_partwise_trans  {hX : X₀ ∪ X₁ = Set.univ} {n : ℕ} {x₀ x₁ x₂ : X} {γ₁ : Dipath x₀ x₁}
  {γ₂ : Dipath x₁ x₂} (hγ₁ : covered_partwise hX γ₁ n) (hγ₂ : covered_partwise hX γ₂ n) :
    covered_partwise hX (γ₁.trans γ₂) (n + n).succ := by
  apply covered_partwise_of_covered_by_intervals
  intros i hi
  have h_lt : n.succ < (n + n).succ.succ := by linarith
  have h₁ : Fraction (Nat.succ_pos (n + n).succ) (le_of_lt h_lt) = Fraction (two_pos) (le_of_lt one_lt_two) := by
    simp
    rw [←one_div]
    apply (div_eq_div_iff _ _).mpr
    ring
    have : (n : ℝ) ≥ 0 := Nat.cast_nonneg n
    linarith
    linarith

  by_cases h : i < n.succ
  · rw [←SplitProperties.firstPart_range_interval_partial_coe (γ₁.trans γ₂) h_lt h]
    rw [SplitProperties.firstPart_eq_of_split_point_eq (γ₁.trans γ₂) h₁]
    rw [SplitProperties.first_part_trans γ₁ γ₂]
    rw [Dipath.cast_image, Dipath.cast_image]
    exact covered_by_intervals_of_covered_partwise n hγ₁ i h
  · set k := i - n.succ with k_def
    push_neg at h
    rw [show i = k + n.succ by rw [k_def, Nat.sub_add_cancel]; exact h]
    have hn : (n + n).succ - n = n.succ := by rw [Nat.succ_sub, Nat.add_sub_cancel]; exact Nat.le_add_right n n
    have hn' : (↑(n + n).succ : ℝ) - ↑n = ↑n + 1 := by
      rw [←Nat.cast_succ n, ←hn, Nat.cast_sub]
      exact le_of_lt (Nat.lt_of_succ_lt_succ h_lt)
    have : i < n.succ + n.succ := by linarith
    have hk : k < n.succ := k_def ▸ (tsub_lt_iff_left h).mpr this
    have hk' : k < (n + n).succ - n := hn.symm ▸ hk
    rw [←SplitProperties.secondPart_range_partial_interval_coe (γ₁.trans γ₂) h_lt hk']
    rw [SplitProperties.secondPart_eq_of_split_point_eq (γ₁.trans γ₂) h₁]
    rw [SplitProperties.second_part_trans γ₁ γ₂]
    rw [Dipath.cast_image, Dipath.cast_image, hn']
    exact covered_by_intervals_of_covered_partwise n hγ₂ k hk

lemma has_interval_division {X₁ X₂ : Set X} (hX : X₁ ∪ X₂ = Set.univ) (X₁_open : IsOpen X₁)
  (X₂_open : IsOpen X₂) (γ : Dipath x₀ x₁) :
    ∃ (n : ℕ), (n > 0) ∧ ∀ (i : ℕ) (_ : i < n),
      Set.Icc ((i:ℝ)/(n:ℝ)) ((i+1:ℝ)/(n:ℝ)) ⊆ γ.extend ⁻¹' X₁ ∨
      Set.Icc ((i:ℝ)/(n:ℝ)) ((i+1:ℝ)/(n:ℝ)) ⊆ γ.extend ⁻¹' X₂ := by
  set c : ℕ → Set ℝ := fun i => if i = 0 then γ.extend ⁻¹' X₁ else γ.extend ⁻¹'  X₂ with c_def
  have h₁ : ∀ i, IsOpen (c i) := by
    intro i
    rw [c_def]
    by_cases i = 0
    case pos h =>
      simp [h]
      exact (Path.continuous_extend γ.toPath).isOpen_preimage X₁ X₁_open
    case neg h =>
      simp [h]
      exact (Path.continuous_extend γ.toPath).isOpen_preimage X₂ X₂_open

  have h₂ : I ⊆ ⋃ (i : ℕ), c i := by
    intros x _
    simp [c_def]
    have : γ.extend x ∈ X₁ ∪ X₂ := hX.symm ▸ (Set.mem_univ $ γ.extend x)
    cases this
    case inl h => use 0; simp; exact h
    case inr h => use 1; simp; exact h

  rcases (lebesgue_number_lemma_unit_interval h₁ h₂) with ⟨n, n_pos, hn⟩
  use n
  constructor
  · exact n_pos
  · intros i hi
    cases (hn i hi)
    rename_i j hj
    rw [c_def] at hj
    simp at hj
    by_cases j = 0
    case pos h => left; convert hj; simp [h]
    case neg h => right; convert hj; simp [h]

/--
  If `γ` is a dipath and a directed space `X` is covered by two opens `X₁` and `X₂`, then `γ` is n-covered for some `n`.
-/
lemma has_subpaths {X₁ X₂ : Set X} (hX : X₁ ∪ X₂ = Set.univ) (X₁_open : IsOpen X₁)
  (X₂_open : IsOpen X₂) (γ : Dipath x₀ x₁) :
    ∃ (n : ℕ), covered_partwise hX γ n := by
  have := has_interval_division hX X₁_open X₂_open γ
  rcases this with ⟨n, n_pos, hn⟩
  use n-1
  apply covered_partwise_of_covered_by_intervals
  simp
  intros i hi
  have h : n - 1 + 1 = n := Nat.succ_pred_eq_of_pos n_pos
  have := hn i (by linarith)
  convert this <;> nth_rewrite 2 [←h] <;> simp

end covered_partwise
end Dipath

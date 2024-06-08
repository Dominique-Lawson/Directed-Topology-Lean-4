import Lean4.path_cover
import Lean4.split_dihomotopy

/-
  This file contains the definition of a (n, m)-covered (dipath) dihomotopy, covered by X₁ and X₂:
      It maps all subrectangles  [i/n, (i+1)/n] × [j/m, (j+1)/m] into either X₁ or X₂

  Conditions for being (n, m)-covered are given.

  Two paths are called (n, m)-dihomotopic if a (n, m)-covered path dihomotopy between them exists.
-/

open Set DirectedMap
open scoped unitInterval

noncomputable section

namespace DirectedMap
namespace Dihomotopy

variable {X : dTopCat} {f g : D(I, X)} {X₀ X₁ : Set X}

/--
  A dihomotopy of directed maps is covered if its image lies entirely in X₀ or in X₁.
-/
def covered (F : Dihomotopy f g) (_ : X₀ ∪ X₁ = univ) : Prop := range F ⊆ X₀ ∨ range F ⊆ X₁

/--
  A dihomotopy of directed maps is covered partwise n m if it can be covered by
  rectangles (n+1 vertically, m+1 horizontally) such that each rectangle is covered by either X₀ or X₁
-/
def coveredPartwise (_ : X₀ ∪ X₁ = univ) (F : Dihomotopy f g) (n m : ℕ) : Prop :=
  ∀ (i j : ℕ) (hi : i < n.succ) (hj : j < m.succ),
    F '' (UnitSubrectangle hi hj) ⊆ X₀ ∨ F '' (UnitSubrectangle hi hj) ⊆ X₁

/--
  A dihomotopy that can be covered partwise by `1 × 1` squares is covered.
-/
lemma covered_of_coveredPartwise {F : Dihomotopy f g} {hX : X₀ ∪ X₁ = univ} (hF : coveredPartwise hX F 0 0) :
    covered F hX := by
  unfold covered
  cases hF 0 0 zero_lt_one zero_lt_one
  case inl h =>
    left
    rintro x ⟨⟨t₀, t₁⟩, ht⟩
    rw [←ht]
    exact h ⟨(t₀, t₁), UnitSubrectangle.mem_unitSquare _, rfl⟩
  case inr h =>
    right
    rintro x ⟨⟨t₀, t₁⟩, ht⟩
    rw [←ht]
    exact h ⟨(t₀, t₁), UnitSubrectangle.mem_unitSquare _, rfl⟩

/--
If `F : f ∼ g` is a dihomotopy of directed maps, then the image of `f` restricted to `[i/(m+1), (i+1)/(m+1)]`
is contained in the image of `F` restricted to `[0, 1/(n+1)] × [i/(m+1), (i+1)/(m+1)]`.
-/
lemma left_path_image_interval_subset_of_dihomotopy_subset (F : Dihomotopy f g) (n : ℕ) {i m : ℕ} (hi : i < m.succ) :
    (Dipath.of_directedMap f).toPath.extend '' Icc (↑i / (↑m + 1)) ((↑i + 1) / (↑m + 1)) ⊆
      F ''  UnitSubrectangle (Nat.succ_pos n) hi := by
  rintro x ⟨t, ⟨ht, rfl⟩⟩
  have tI : t ∈ I := UnitIntervalSub.mem_I_of_mem_interval_coed hi ht
  rw [Path.extend_extends (Dipath.of_directedMap f).toPath tI]
  use (0, ⟨t, tI⟩)
  constructor
  · apply UnitSubrectangle.mem_unitSubrectangle
    constructor
    · norm_num
    · apply div_nonneg
      · norm_num
      · exact Nat.cast_nonneg _
    · convert ht <;> exact Nat.cast_succ _
  · simp; rfl

/--
If `F : f ∼ g` is a dihomotopy of directed maps, and `F` is `n × m`-covered, then `f` is `m`-covered.
-/
lemma path_covered_partiwse_of_dihomotopy_coveredPartwise_left {F : Dihomotopy f g} {hX : X₀ ∪ X₁ = univ}
  {n m : ℕ} (hF : coveredPartwise hX F n m) :
    Dipath.covered_partwise hX (Dipath.of_directedMap f) m := by
  apply Dipath.covered_partwise.covered_partwise_of_covered_by_intervals
  intros i hi
  cases hF 0 i (Nat.succ_pos n) hi
  case a.inl h =>
    left
    exact subset_trans (left_path_image_interval_subset_of_dihomotopy_subset F n hi) h
  case a.inr h =>
    right
    exact subset_trans (left_path_image_interval_subset_of_dihomotopy_subset F n hi) h

/--
If `F : f ∼ g` is a dihomotopy of directed maps, then the image of `g` restricted to `[i/(m+1), (i+1)/(m+1)]`
is contained in the image of `F` restricted to `[n/(n+1), 1] × [i/(m+1), (i+1)/(m+1)]`.
-/
lemma right_path_image_interval_subset_of_dihomotopy_subset (F : Dihomotopy f g) (n : ℕ) {i m : ℕ} (hi : i < m.succ) :
    (Dipath.of_directedMap g).toPath.extend '' Icc (↑i / (↑m + 1)) ((↑i + 1) / (↑m + 1)) ⊆
      F ''  UnitSubrectangle (Nat.lt_succ_self n) hi := by
  rintro x ⟨t, ⟨ht, rfl⟩⟩
  have tI : t ∈ I := UnitIntervalSub.mem_I_of_mem_interval_coed hi ht
  rw [Path.extend_extends (Dipath.of_directedMap g).toPath tI]
  use (1, ⟨t, tI⟩)
  constructor
  · apply UnitSubrectangle.mem_unitSubrectangle
    · constructor
      · exact (div_le_one (show (n.succ : ℝ) > 0 by
          exact Nat.cast_pos.mpr (Nat.succ_pos n))).mpr (Nat.cast_le.mpr (Nat.le_succ n))
      · rw [div_self]
        exact Nat.cast_ne_zero.mpr (ne_of_gt (Nat.succ_pos n))
    · convert ht <;> exact Nat.cast_succ _
  · simp; rfl

/--
If `F : f ∼ g` is a dihomotopy of directed maps, and `F` is `n × m`-covered, then `g` is `m`-covered.
-/
lemma path_covered_partiwse_of_dihomotopy_coveredPartwise_right {F : Dihomotopy f g}
  {hX : X₀ ∪ X₁ = univ} {n m : ℕ} (hF : coveredPartwise hX F n m) :
    Dipath.covered_partwise hX (Dipath.of_directedMap g) m := by
  apply Dipath.covered_partwise.covered_partwise_of_covered_by_intervals
  intros i hi
  cases hF n i (Nat.lt_succ_self n) hi
  case a.inl h =>
    left
    exact subset_trans (right_path_image_interval_subset_of_dihomotopy_subset F n hi) h
  case a.inr h =>
    right
    exact subset_trans (right_path_image_interval_subset_of_dihomotopy_subset F n hi) h

/--
If `F : f ∼ g` is a dihomotopy of directed maps, there exist `n m : ℕ` such that `F` is `n × m`-covered.
-/
lemma coveredPartwise_exists (F : Dihomotopy f g) (hX : X₀ ∪ X₁ = univ) (X₀_open : IsOpen X₀) (X₁_open : IsOpen X₁) :
    ∃ (n m : ℕ), coveredPartwise hX F n m := by
  set c : ℕ → Set (I × I) := fun i => if i = 0 then F ⁻¹' X₀ else F ⁻¹'  X₁ with c_def
  have h₁ : ∀ i, IsOpen (c i) := by
    intro i
    by_cases i = 0
    case pos  h =>
      simp [h]
      exact F.continuous_toFun.isOpen_preimage X₀ X₀_open
    case neg h =>
      simp [h]
      exact F.continuous_toFun.isOpen_preimage X₁ X₁_open

  have h₂ : UnitSquare ⊆ (⋃ (i : ℕ), c i) := by
    intros x _
    simp
    have : F x ∈ X₀ ∪ X₁ := hX.symm ▸ (Set.mem_univ $ F x)
    cases this
    case inl h => use 0; simp; exact h
    case inr h => use 1; simp; exact h

  rcases (lebesgue_number_lemma_unit_square h₁ h₂) with ⟨n, hn⟩
  use n
  use n
  intros i j hi hj
  cases (hn i j hi hj)
  case h.intro ι hι =>
    rw [c_def] at hι
    simp at hι
    by_cases ι = 0
    case pos h => left; simp [h] at hι; exact Set.image_subset_iff.mpr hι
    case neg h => right; simp [h] at hι; exact Set.image_subset_iff.mpr hι

/--
  The image of a dihomotopy F of the subrectangles `[0, 1/(n+2)] × [j/(m+1), (j+1)/(m+1)]`
  contains the image of the first part of F, split at `1/(n+2)`, of `[0, 1] × [j/(m+1), (j+1)/(m+1)]`.
-/
lemma fpv_subrectangle {x y : X} {γ₁ γ₂ : Dipath x y} {F : Dipath.Dihomotopy γ₁ γ₂} {n m j : ℕ} (hj : j < m.succ) :
    (SplitDihomotopy.FirstPartVerticallyDihomotopy F (Fraction.ofPos (Nat.succ_pos n.succ))).toDihomotopy ''
    (UnitSubrectangle zero_lt_one hj) ⊆ F '' (UnitSubrectangle (Nat.zero_lt_succ n.succ) hj) := by
  rintro z ⟨⟨t₀, t₁⟩, ⟨tI, ht⟩⟩
  have : ((SplitDihomotopy.FirstPartVerticallyDihomotopy F _).toDihomotopy) (t₀, t₁) =
    (SplitDihomotopy.FirstPartVerticallyDihomotopy F (Fraction.ofPos (Nat.succ_pos n.succ))) (t₀, t₁) := rfl
  rw [this, SplitDihomotopy.fpv_apply] at ht
  show ∃ a, a ∈ UnitSubrectangle _ hj ∧ F a = z
  refine' ⟨_, _, ht⟩
  constructor
  constructor
  · rw [Fraction.eq_zero]
    unit_interval
  · exact unitInterval.mul_le_left
  · exact tI.2

/--
  If F is `(n+1) × m`-covered, then the first part of F, split at `T = 1/(n+2)` is `0 x m`-covered.
-/
lemma coveredPartwise_first_vpart {x y : X} {γ₁ γ₂ : Dipath x y} {F : Dipath.Dihomotopy γ₁ γ₂}
  {hX : X₀ ∪ X₁ = univ} {n m : ℕ} (hF : coveredPartwise hX F.toDihomotopy n.succ m) :
    coveredPartwise hX (SplitDihomotopy.FirstPartVerticallyDihomotopy F
      (Fraction.ofPos (Nat.succ_pos n.succ))).toDihomotopy 0 m := by
  unfold coveredPartwise at hF
  unfold coveredPartwise
  intros i j hi hj
  obtain ⟨rfl⟩ : i = 0 := by linarith
  cases (hF 0 j (Nat.succ_pos n.succ) hj)
  case refl.inl h => left; exact subset_trans (fpv_subrectangle _) h
  case refl.inr h => right; exact subset_trans (fpv_subrectangle _) h

/--
  If `i/(n+1) ≤ t`, then `(i+1)/(n+2) ≤ (σ q) * t + q`, where `q = 1/(n+2)`
-/
lemma spv_aux₁_coed {t : ℝ} {n i : ℕ} (_ : i < n.succ) (ht : (i : ℝ)/(n.succ : ℝ) ≤ t) :
    (i+1 : ℝ) / (n+2 : ℝ) ≤ (1 - 1/(n+1+1)) * t + (1/(n+1+1)) := by
  have h₀ : 0 ≤ (i : ℝ)/(n.succ : ℝ) := by
    apply div_nonneg
    exact Nat.cast_nonneg i
    exact Nat.cast_nonneg n.succ
  have h₁ : 0 ≤ t := le_trans h₀ ht
  have h₂ : (n.succ : ℝ) > 0 := Nat.cast_pos.mpr (Nat.succ_pos n)
  have h₃ : 0 ≤ (n : ℝ) + 1 := by
    apply le_of_lt
    rw [Nat.cast_succ _] at h₂
    exact h₂

  rw [FractionEqualities.one_sub_inverse_of_add_one, mul_comm, mul_div, div_add_div_same]

  apply div_le_div
  · linarith [mul_nonneg h₁ h₃]
  · apply add_le_add_right
    calc (i : ℝ)
      _ = ↑i * 1                      := by rw [mul_one]
      _ = ↑i * ((↑n.succ)/(↑n.succ))  := by rw [div_self (ne_of_gt h₂)]
      _ = ↑i/(↑n.succ) * (↑n.succ)    := by ring
      _ ≤ t * (↑n.succ)               := mul_le_mul_of_le_of_le ht (le_refl _) h₀ (le_of_lt h₂)
      _ = t * (↑n+1)                  := by rw [Nat.cast_succ]
  · linarith
  · linarith
  · linarith

/--
  If `i/(n+1) ≤ t`, then `(i+1)/(n+2) ≤ (σ q) * t + q`, where `q = 1/(n+2)`
-/
lemma spv_aux₁ {t : I} {n i : ℕ} (hi : i < n.succ) (ht : Fraction (Nat.succ_pos n) (le_of_lt hi) ≤ t) :
  Fraction (Nat.succ_pos n.succ) (le_of_lt (Nat.succ_lt_succ hi)) ≤
    (⟨_, interp_left_mem_I (Fraction (Nat.succ_pos n.succ) (Nat.succ_le_succ (Nat.zero_le n.succ))) t⟩ : I) := by
  apply Subtype.coe_le_coe.mp
  convert spv_aux₁_coed hi ht using 1
  rw [Fraction.Fraction_coe]
  congr 1 <;> simp; ring
  simp

/--
  If `t ≤ (i+1)/(n+1)`, then `(σ q) * t + q ≤ (i+2)/(n+2)`, where `q = 1/(n+2)`
-/
lemma spv_aux₂_coed {t : ℝ} {n i : ℕ} (_ : i < n.succ) (ht₀ : 0 ≤ t) (ht : t ≤ (i.succ : ℝ)/(n.succ : ℝ)) :
    (1 - 1/(n+1+1 : ℝ)) * t + (1/(n+1+1 : ℝ)) ≤ (i+2 : ℝ) / (n+2 : ℝ) := by
  have h₀ : (n.succ : ℝ) > 0 := Nat.cast_pos.mpr (Nat.succ_pos n)
  have h₁ : (n : ℝ) ≥ 0 := Nat.cast_nonneg n
  have h₂ : (i : ℝ) ≥ 0 := Nat.cast_nonneg i
  rw [FractionEqualities.one_sub_inverse_of_add_one, mul_comm, mul_div, div_add_div_same]
  apply div_le_div <;> try linarith
  · rw [←one_add_one_eq_two, ←add_assoc]
    apply add_le_add_right
    calc t * (n + 1 : ℝ)
      _ = t * (↑n.succ)                   := by rw [Nat.cast_succ]
      _ ≤ (↑i.succ)/(↑n.succ) * (↑n.succ) := mul_le_mul_of_le_of_le ht (le_refl _) ht₀ (le_of_lt h₀)
      _ = (↑n.succ)/(↑n.succ) * (↑i.succ) := by ring
      _ = 1 * (↑i.succ)                   := by rw [div_self (ne_of_gt h₀)]
      _ = (↑i.succ)                       := one_mul _
      _ = (↑i + 1)                        := by rw [Nat.cast_succ]
  linarith

/--
  If `t ≤ (i+1)/(n+1)`, then `(σ q) * t + q ≤ (i+2)/(n+2)`, where `q = 1/(n+2)`
-/
lemma spv_aux₂ {t : I} {n i : ℕ} (hi : i < n.succ) (ht : t ≤ Fraction (Nat.succ_pos n) (Nat.succ_le_of_lt hi)) :
    (⟨_, interp_left_mem_I (Fraction (Nat.succ_pos n.succ) (Nat.succ_le_succ (Nat.zero_le n.succ))) t⟩ : I) ≤
      Fraction (Nat.succ_pos n.succ) (Nat.succ_le_of_lt (Nat.succ_lt_succ hi)) := by
  apply Subtype.coe_le_coe.mp
  convert spv_aux₂_coed hi t.2.1 ht using 1
  simp
  rw [Fraction.Fraction_coe]
  congr 1 <;> rw [Nat.cast_succ, Nat.cast_succ] <;> linarith

/--
  The image of a dihomotopy F of the subrectangle `[(i+1)/(n+2), (i+2)/(n+2)] × [j/(m+1), (j+1)/(m+1)]`
  contains the image of the second part of F, split at `1/(n+2)`, of `[i/(n+1), (i+1)/(n+1)] × [j/(m+1), (j+1)/(m+1)]`.
-/
lemma spv_subrectangle {x y : X} {γ₁ γ₂ : Dipath x y} {F : Dipath.Dihomotopy γ₁ γ₂} {n m i j : ℕ}
  (hi : i < n.succ) (hj : j < m.succ) :
    (SplitDihomotopy.SecondPartVerticallyDihomotopy F (Fraction.ofPos (Nat.succ_pos n.succ))).toDihomotopy ''
    (UnitSubrectangle hi hj) ⊆ F '' (UnitSubrectangle (Nat.succ_lt_succ hi) hj) := by
  rintro z ⟨⟨t₀, t₁⟩, ⟨tI, ht⟩⟩
  have : ((SplitDihomotopy.SecondPartVerticallyDihomotopy F _).toDihomotopy) (t₀, t₁) =
          (SplitDihomotopy.SecondPartVerticallyDihomotopy F (Fraction.ofPos (Nat.succ_pos n.succ))) (t₀, t₁) := rfl
  rw [this, SplitDihomotopy.spv_apply] at ht
  show ∃ a, a ∈ UnitSubrectangle _ hj ∧ F a = z
  refine' ⟨_, _, ht⟩
  constructor
  constructor
  · exact spv_aux₁ hi tI.1.1
  · exact spv_aux₂ hi tI.1.2
  · exact tI.2

/--
  If F is  `(n + 1) × m`-covered, then the second part of F, split at `T = 1/(n+1)` is `n × m`-covered.
-/
lemma coveredPartwise_second_vpart {x y : X} {γ₁ γ₂ : Dipath x y} {F : Dipath.Dihomotopy γ₁ γ₂}
  {hX : X₀ ∪ X₁ = univ} {n m : ℕ} (hF : coveredPartwise hX F.toDihomotopy n.succ m) :
    coveredPartwise hX (SplitDihomotopy.SecondPartVerticallyDihomotopy F
      (Fraction.ofPos (Nat.succ_pos n.succ))).toDihomotopy n m := by
  unfold coveredPartwise at hF
  unfold coveredPartwise
  intros i j hi hj
  cases (hF i.succ j (Nat.succ_lt_succ hi) hj)
  case inl h => left; exact subset_trans (spv_subrectangle _ _) h
  case inr h => right; exact subset_trans (spv_subrectangle _ _) h

/--
  The image of a dihomotopy F of the rectangle `[i/(n+1), (i+1)/(n+1)] × [0, 1/(m+2)]`
  contains the image of the first part of F, split at `1/(m+2)`, of `[i/(n+1), (i+1)/(n+1)] × [0, 1]`.
-/
lemma fph_subrectangle {f g : D(I, X)} {F : Dihomotopy f g} {n m i : ℕ} (hi : i < n.succ) :
    (SplitDihomotopy.FirstPartHorizontallyDihomotopy F (Fraction.ofPos (Nat.succ_pos m.succ))) ''
      (UnitSubrectangle hi zero_lt_one) ⊆ F '' (UnitSubrectangle hi (Nat.succ_pos m.succ)) := by
  rintro z ⟨⟨t₀, t₁⟩, ⟨tI, ht⟩⟩
  rw [SplitDihomotopy.fph_apply] at ht
  show ∃ a, a ∈ UnitSubrectangle hi _ ∧ F a = z
  refine' ⟨_, _, ht⟩
  constructor
  · exact tI.1
  · constructor
    · rw [Fraction.eq_zero]
      unit_interval
    · exact unitInterval.mul_le_left

/--
  If `F` is `n × (m+1)`-covered, then the first part of `F`, split at `T = 1/(m+2)`, is `n × 0`-covered.
-/
lemma coveredPartwise_first_hpart {f g : D(I, X)} {F : Dihomotopy f g} {hX : X₀ ∪ X₁ = univ} {n m : ℕ}
  (hF : coveredPartwise hX F n m.succ) :
    coveredPartwise hX (SplitDihomotopy.FirstPartHorizontallyDihomotopy F
      (Fraction.ofPos (Nat.succ_pos m.succ))) n 0 := by
  unfold coveredPartwise at hF
  unfold coveredPartwise
  intros i j hi hj
  obtain ⟨rfl⟩ : j = 0 := by linarith
  cases (hF i 0 hi (Nat.succ_pos m.succ))
  case refl.inl h => left; exact subset_trans (fph_subrectangle _) h
  case refl.inr h => right; exact subset_trans (fph_subrectangle _) h

/--
  The image of a dihomotopy F of the rectangle `[i/(n+1), (i+1)/(n+1)] × [(j+1)/(m+2), (j+2)/(m+2)]`
  contains the image of the second part of F, split at `1/(m+2)`, of
  `[i/(n+1), (i+1)/(n+1)] × [j/(m+1), (j+1)/(m+1)]`.
-/
lemma sph_subrectangle {f g : D(I, X)} {F : Dihomotopy f g} {n m i j : ℕ} (hi : i < n.succ) (hj : j < m.succ) :
    (SplitDihomotopy.SecondPartHorizontallyDihomotopy F (Fraction.ofPos (Nat.succ_pos m.succ))) ''
      (UnitSubrectangle hi hj) ⊆ F '' (UnitSubrectangle hi (Nat.succ_lt_succ hj)) := by
  rintro z ⟨⟨t₀, t₁⟩, ⟨tI, ht⟩⟩
  rw [SplitDihomotopy.sph_apply] at ht
  show ∃ a, a ∈ UnitSubrectangle hi _ ∧ F a = z
  refine' ⟨_, _, ht⟩
  constructor
  · exact tI.1
  · constructor
    · exact spv_aux₁ hj tI.2.1
    · exact spv_aux₂ hj tI.2.2

/--
  If `F` is `n × (m+1)`-covered, then the second part of `F`, split at at `T = 1/(n+1)` is `n × m`-covered.
-/
lemma coveredPartwise_second_hpart {f g : D(I, X)} {F : Dihomotopy f g} {hX : X₀ ∪ X₁ = univ} {n m : ℕ}
  (hF : coveredPartwise hX F n m.succ) :
    coveredPartwise hX (SplitDihomotopy.SecondPartHorizontallyDihomotopy F
      (Fraction.ofPos (Nat.succ_pos m.succ))) n m := by
  unfold coveredPartwise at hF
  unfold coveredPartwise
  intros i j hi hj
  cases (hF i j.succ hi (Nat.succ_lt_succ hj))
  case inl h => left; exact subset_trans (sph_subrectangle _ _) h
  case inr h => right; exact subset_trans (sph_subrectangle _ _) h

end Dihomotopy
end DirectedMap

namespace Dipath
namespace Dihomotopy

variable {X : dTopCat} {X₀ X₁ : Set X} {x y : X} {γ₁ γ₂ : Dipath x y}

lemma range_left_subset (F : Dihomotopy γ₁ γ₂) : range γ₁ ⊆ range F :=
  fun _ ⟨t, ht⟩ => ⟨(0 , t), ht ▸ F.map_zero_left t⟩

lemma range_right_subset (F : Dihomotopy γ₁ γ₂) : range γ₂ ⊆ range F :=
  fun _ ⟨t, ht⟩ => ⟨(1 , t), ht ▸ F.map_one_left t⟩

/--
  A dihomotopy of directed paths is covered if its image lies entirely in X₀ or in X₁.
-/
def covered (_ : X₀ ∪ X₁ = univ) (F : Dihomotopy γ₁ γ₂) : Prop := range F ⊆ X₀ ∨ range F ⊆ X₁

/--
If `F : γ₁ ∼ γ₂` is a dihomotopy of directed paths, and `F` is covered, then `γ₁` is covered.
-/
lemma covered_left_of_covered {F : Dihomotopy γ₁ γ₂} {hX : X₀ ∪ X₁ = univ} (hF : covered hX F) :
    Dipath.covered hX γ₁ :=
  Or.elim hF
    (fun hF => Or.inl (subset_trans (range_left_subset F) hF))
    (fun hF => Or.inr (subset_trans (range_left_subset F) hF))

/--
If `F : γ₁ ∼ γ₂` is a dihomotopy of directed paths, and `F` is covered, then `γ₂` is covered.
-/
lemma covered_right_of_covered {F : Dihomotopy γ₁ γ₂} {hX : X₀ ∪ X₁ = univ} (hF : covered hX F) :
    Dipath.covered hX γ₂ :=
  Or.elim hF
    (fun hF => Or.inl (subset_trans (range_right_subset F) hF))
    (fun hF => Or.inr (subset_trans (range_right_subset F) hF))

/--
  Two paths are `m × n`-dihomotopic if there is a dihomotopy between them that can be covered by `m × n` rectangles.
-/
def dihomotopicCovered (hX : X₀ ∪ X₁ = univ) (γ₁ γ₂ : Dipath x y) (n m : ℕ) : Prop :=
  ∃ (F : Dihomotopy γ₁ γ₂), DirectedMap.Dihomotopy.coveredPartwise hX F.toDihomotopy n m

/--
  If `γ₁` and `γ₂` are two paths connected by a path-dihomotopy `F` that is covered by `m × (n + 1)` rectangles,
  then `γ₁` and `F.eval (1/(n+2))` are `m × 0`-dihomotopic and `F.eval (1/(n+2))` and `γ₂` are `m × n`-dihomotopic.
-/
lemma dihomotopicCovered_split {F : Dihomotopy γ₁ γ₂} (hX : X₀ ∪ X₁ = univ) {n m : ℕ}
  (hF : DirectedMap.Dihomotopy.coveredPartwise hX F.toDihomotopy n.succ m) :
    dihomotopicCovered hX γ₁ (F.eval (Fraction.ofPos (Nat.succ_pos n.succ))) 0 m ∧
    dihomotopicCovered hX (F.eval (Fraction.ofPos (Nat.succ_pos n.succ))) γ₂ n m := by
  constructor
  · exact ⟨_, DirectedMap.Dihomotopy.coveredPartwise_first_vpart hF⟩
  · exact ⟨_, DirectedMap.Dihomotopy.coveredPartwise_second_vpart hF⟩

/--
  If `γ₁` and `γ₂` are two directed paths paths such that there is some dihomotopy between them,
  then there are `n m : ℕ` such that `γ₁` and `γ₂` are `n × m`-dihomotopicCovered.
-/
lemma dihomotopicCovered_exists_of_preDihomotopic (hX : X₀ ∪ X₁ = univ) (h : γ₁.PreDihomotopic γ₂)
  (X₀_open : IsOpen X₀) (X₁_open : IsOpen X₁) :
    ∃ (n m : ℕ), dihomotopicCovered hX γ₁ γ₂ n m := by
  rcases (DirectedMap.Dihomotopy.coveredPartwise_exists h.some.toDihomotopy hX X₀_open X₁_open) with ⟨n, m, hnm⟩
  exact ⟨n, m, h.some, hnm⟩


end Dihomotopy
end Dipath

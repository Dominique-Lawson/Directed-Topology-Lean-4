import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.UnitInterval
-- import auxiliary

/-
  This file contains two applications of the Lebesgue Number Lemma:
  One concerns the unit interval and the other concerns the unit square.
-/

universe u

-- open auxiliary
open scoped unitInterval

/-! ### Auxiliary lemmas -/

-- linarith [show (n : ℝ) > 0 by exact Nat.cast_pos.mpr hn]
lemma mid_point_Icc {i n : ℕ} (hn : n > 0) :
    (2 * i + 1 : ℝ)/(2 * n : ℝ) ∈ Set.Icc ((i:ℝ)/(n:ℝ)) ((i+1:ℝ)/(n:ℝ)) := by
  constructor <;>
  refine' (div_le_div_iff _ _).mpr _ <;>
  linarith [show (n : ℝ) > 0 by exact Nat.cast_pos.mpr hn]

lemma mid_point_I {i n : ℕ} (hn : n > 0) (hi : i < n) : (2 * i + 1 : ℝ)/(2 * n : ℝ) ∈ I := by
  have n_cast_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have : 2 * i + 1 ≤ 2 * n := by linarith
  constructor
  · apply div_nonneg
    exact add_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg i)) (by norm_num)
    exact mul_nonneg (by norm_num) (Nat.cast_nonneg n)
  · refine' (div_le_one (mul_pos (by norm_num) n_cast_pos)).mpr _
    have : (↑(2 * i  + 1) : ℝ) ≤ ↑(2 * n) := Nat.cast_le.mpr this
    convert this <;> simp

/-! ### Covering lemma for the unit interval -/

theorem lebesgue_number_lemma_unit_interval {ι : Sort u} {c : ι → Set ℝ}
  (hc₁ : ∀ (i : ι), IsOpen (c i)) (hc₂ : I ⊆ ⋃ (i : ι), c i) :
    ∃ (n : ℕ), (n > 0) ∧ ∀ (i : ℕ) (h : i < n), ∃ (j : ι), Set.Icc ((i : ℝ)/n) ((i+1)/n) ⊆ c j := by
  rcases (lebesgue_number_lemma_of_metric (isCompact_Icc) hc₁ hc₂) with ⟨δ, δ_pos, hδ⟩
  rcases Real.instArchimedean.arch 2 δ_pos with ⟨n, hn⟩

  use n
  have n_pos : 0 < n := by
    by_contra
    have : n = 0 := by linarith
    rw [this] at hn
    have : (2 : ℝ) ≤ 0 := hn
    linarith
  have n_cast_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr n_pos

  constructor
  · exact n_pos

  intros i hi
  have mid_point_I : (2 * i + 1 : ℝ)/(2 * n : ℝ) ∈ I := mid_point_I n_pos hi
  have mid_point_Icc : (2 * i + 1 : ℝ)/(2 * n : ℝ) ∈ Set.Icc ((i:ℝ)/(n:ℝ)) ((i+1:ℝ)/(n:ℝ)) := mid_point_Icc n_pos
  rcases (hδ ((2 * i + 1 : ℝ)/(2 * n : ℝ)) mid_point_I) with ⟨j, hj⟩
  use j
  apply subset_trans _ hj
  intros x hx
  show dist x ((2 * i + 1 : ℝ)/(2 * n : ℝ)) < δ

  have : 1/(n : ℝ) < δ := by
    apply (div_lt_iff' n_cast_pos).mpr
    apply lt_of_lt_of_le (show (1 : ℝ) < (2 : ℝ) by norm_num)
    -- TODO: Improve this
    convert hn
    refine (funext ?h.e'_4.h.e.h).symm
    intro x
    simp

  apply lt_of_le_of_lt _ this
  apply le_trans (Real.dist_le_of_mem_Icc hx mid_point_Icc)
  rw [div_sub_div_same]
  simp

/-! ### Covering lemma for the unit square -/

def unit_square : Set (I × I) := Set.univ

lemma compact_unit_square : IsCompact unit_square := isCompact_univ

/-- The square [i/n, (i+1)/n] × [j/m, (j+1)/m] in the unit interval. -/
def UnitSubsquare {n m i j : ℕ} (hi : i < n.succ) (hj : j < m.succ) : Set (I × I) := sorry

theorem lebesgue_number_lemma_unit_square {ι : Sort u} {c : ι → Set (I × I)} (hc₁ : ∀ (i : ι), IsOpen (c i)) (hc₂ : UnitSquare ⊆ (⋃ (i : ι), c i)) :
  ∃ (n : ℕ), ∀ (i j : ℕ) (hi : i < n.succ) (hj : j < n.succ), ∃ (a : ι), UnitSubsquare hi hj ⊆ c a := sorry

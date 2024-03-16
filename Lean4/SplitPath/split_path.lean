import Lean4.interpolate
import Lean4.unit_interval_aux

/- This file contains definitions for splitting a path `γ : Path x y` at some point `T : I`
  yielding two different paths:
  * Its first part, from `x` to `γ T`, given by evaluating `γ` on `[0, T]`.
  * Its second part, from `γ T` to `y`, given by evaluating `γ` on `[T, 1]`.
-/

open scoped unitInterval

noncomputable section

universe u

variable {X : Type u} [DirectedSpace X] {x₀ x₁ : X}

namespace SplitPath

/-- The part of a path on the interval [0, T] -/
def FirstPart (γ : Path x₀ x₁) (T : I) : Path x₀ (γ T) where
  toFun := fun t => γ ⟨(T : ℝ) * ↑t, unitInterval.mul_mem T.2 t.2⟩
  source' := by simp [γ.source']
  target' := by simp

/-- The part of a path on the interval [T, 1] -/
def SecondPart (γ : Path x₀ x₁) (T : I) : Path (γ T) x₁ where
  toFun := fun t => γ ⟨(σ T : ℝ) * ↑t + ↑T, interp_left_mem_I T t⟩
  source' := by simp
  target' := by simp [γ.target']

/--
  The map needed to reparametrize the concatenation of the first and second part of a path
  back into the original pat
-/
def trans_reparam (T t : I) : ℝ :=
if (t : ℝ) ≤ (T : ℝ) then
  t / (2 * T)
else
  (1 + t - 2*T) / (2 * (1-T))

@[continuity]
lemma continuous_trans_reparam {T : I} (hT₀ : 0 < T) (hT₁ : T < 1) : Continuous (trans_reparam T) := by
  refine' continuous_if_le _ _ (Continuous.continuousOn _) (Continuous.continuousOn _) _
  · continuity
  · continuity
  · continuity
  · continuity
  intro x hx
  apply (div_eq_div_iff (ne_of_gt (unitIAux.double_pos_of_pos hT₀)) (ne_of_gt (unitIAux.double_sigma_pos_of_lt_one hT₁))).mpr
  simp [hx]
  ring

lemma trans_reparam_mem_I (t : I) {T : I} (hT₀ : 0 < T) (hT₁ : T < 1): trans_reparam T t ∈ I := by
  unfold trans_reparam
  split
  case inl h₀ =>
    constructor
    · exact div_nonneg t.2.1 (le_of_lt (unitIAux.double_pos_of_pos hT₀))
    · apply (div_le_one (unitIAux.double_pos_of_pos hT₀)).mpr
      have : 0 < (T : ℝ) := hT₀
      have : (T : ℝ) ≤ (2 * T : ℝ) := by linarith only [this]
      apply le_trans h₀ this
  case inr h₀ =>
    constructor
    · apply div_nonneg _ (le_of_lt (unitIAux.double_sigma_pos_of_lt_one hT₁))
      linarith [unitIAux.double_sigma_pos_of_lt_one hT₁]
    · exact (div_le_one (unitIAux.double_sigma_pos_of_lt_one hT₁)).mpr (by
      linarith only [unitInterval.le_one t])

lemma trans_reparam_zero (T : I) : trans_reparam T 0 = 0 := by
  unfold trans_reparam
  simp
  intro hT
  linarith [unitInterval.nonneg T]

lemma trans_reparam_one {T : I} (hT₁ : T < 1): trans_reparam T 1 = 1 := by
  unfold trans_reparam
  split_ifs
  case pos h =>
    exfalso
    exact lt_irrefl T (lt_of_lt_of_le hT₁ (Subtype.coe_le_coe.mp h))
  case neg h =>
    apply (div_eq_one_iff_eq _).mpr
    · show (1 : ℝ) + 1 - 2 * T = 2 * (1 - T)
      ring
    · simp
      have h₁ : T ≠ 1 := ne_of_lt hT₁
      exact fun h₂ => h₁ (Subtype.coe_inj.mp ((sub_eq_zero.mp h₂).symm))

lemma monotone_trans_reparam {T : I} (hT₀ : 0 < T) (hT₁ : T < 1) : Monotone (trans_reparam T) := by
  intro x y hxy
  unfold trans_reparam
  split_ifs with h₁ h₂
  · exact (div_le_div_right (unitIAux.double_pos_of_pos hT₀)).mpr hxy
  · apply (div_le_div_iff (unitIAux.double_pos_of_pos hT₀) (unitIAux.double_sigma_pos_of_lt_one hT₁)).mpr
    have : 0 ≤ (T : ℝ) * (↑y - ↑T) := mul_nonneg T.2.1 (by linarith)
    calc (x : ℝ) * (2 * (1 - ↑T))
      _ ≤  ↑T * (2 * (1 - ↑T))                    := (mul_le_mul_right (unitIAux.double_sigma_pos_of_lt_one hT₁)).mpr h₁
      _ ≤  ↑T * (2 * (1 - ↑T)) + ↑T * (↑y - ↑T)   := le_add_of_nonneg_right (mul_nonneg T.2.1 (by linarith))
      _ ≤ (1 + ↑y - 2 * ↑T)  * (2 * ↑T)           := by linarith
  · linarith [Subtype.coe_le_coe.mpr hxy]
  · apply (div_le_div_right (unitIAux.double_sigma_pos_of_lt_one hT₁)).mpr
    linarith [Subtype.coe_le_coe.mpr hxy]

lemma first_trans_second_reparam_eq_self_aux (γ : Path x₀ x₁) (t : I) {T: I} (hT₀ : 0 < T) (hT₁ : T < 1) :
    γ t = ((FirstPart γ T).trans (SecondPart γ T)).reparam
    (fun t => ⟨trans_reparam T t, trans_reparam_mem_I t hT₀ hT₁⟩)
    (by continuity)
    (Subtype.ext $ trans_reparam_zero T) (Subtype.ext $ trans_reparam_one hT₁) t := by

  have hT_ne_zero : (T : ℝ) ≠ 0 := (lt_iff_le_and_ne.mp (Subtype.coe_lt_coe.mpr hT₀)).2.symm
  rw [Path.reparam]
  simp [Path.trans_apply, FirstPart, SecondPart, trans_reparam]
  split_ifs with h₁ h₂ h₂
  · congr
    apply Subtype.coe_inj.mp
    simp
    calc (t : ℝ)
      _ = t * 1 := (mul_one (t : ℝ)).symm
      _ = t * ((2 * T) / (2 * T)) := by rw [div_self (mul_ne_zero two_ne_zero hT_ne_zero)]
      _ = T * (2 * (t / (2 * T))) := by ring
  · exfalso
    have hT_lt_t : ↑T < ↑t := by
      simp at h₂
      calc (T : ℝ)
        _ = 1 * T                     := (one_mul (T : ℝ)).symm
        _ = (2⁻¹ * 2) * T             := by norm_num
        _ = 2⁻¹ * (2 * T)             := by ring
        _ < (t / (2 * T)) * (2 * T) := (mul_lt_mul_right $ unitIAux.double_pos_of_pos hT₀).mpr h₂
        _ = t * ((2 * T) / (2 * T)) := by ring
        _ = t * 1                     := by rw [div_self (mul_ne_zero two_ne_zero hT_ne_zero)]
        _ = t                         := (mul_one (t : ℝ))
    exact not_le_of_lt hT_lt_t h₁
  · exfalso
    have : (1 + (t : ℝ) - 2 * ↑T) ≤ (1 - ↑T) := by
      rw [div_le_iff (unitIAux.double_sigma_pos_of_lt_one hT₁)] at h₂
      simp at h₂
      simp [h₂]
    apply h₁ (Subtype.coe_le_coe.mp _)
    linarith
  · congr
    apply Subtype.coe_inj.mp
    simp
    calc (t : ℝ)
      _ = (1 + t - 2 * T) - 1 + 2 * T := by ring
      _ = (1 + t - 2 * T) * (2 * (1 - T)) / (2 * (1 - T)) - 1 + 2 * ↑T
            := by simp [mul_div_cancel ((1 : ℝ) + t - 2 * T) (ne_of_gt (unitIAux.double_sigma_pos_of_lt_one hT₁))]
      _ = (1 - T) * (2 * ((1 + t - 2 * T) / (2 * (1 - T))) - 1) + T := by ring

lemma first_trans_second_reparam_eq_self (γ : Path x₀ x₁) {T: I} (hT₀ : 0 < T) (hT₁ : T < 1) :
    γ = ((FirstPart γ T).trans (SecondPart γ T)).reparam
    (fun t => ⟨trans_reparam T t, trans_reparam_mem_I t hT₀ hT₁⟩)
    (by continuity)
    (Subtype.ext $ trans_reparam_zero T) (Subtype.ext $ trans_reparam_one hT₁) := by
  ext t
  exact first_trans_second_reparam_eq_self_aux γ t hT₀ hT₁

end SplitPath

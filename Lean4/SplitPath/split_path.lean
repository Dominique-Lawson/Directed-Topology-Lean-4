import Lean4.interpolate
import Lean4.unit_interval_aux

/-
  This file contains lemmas about splitting a (di)path into two parts,
  and how their concatenation relates to the original (di)path
-/

open scoped unitInterval

noncomputable section

universe u

variable {X : Type u} [DirectedSpace X] {x₀ x₁ : X}

namespace SplitPath

/-- The part of a path on the interval [0, T] -/
def FirstPart (γ : Path x₀ x₁) (T : I) : Path x₀ (γ T) :=
{
  toFun := fun t => γ ⟨(T : ℝ) * ↑t, unitInterval.mul_mem T.2 t.2⟩,
  source' := by simp [γ.source'],
  target' := by simp,
}

/-- The part of a path on the interval [T, 1] -/
def SecondPart (γ : Path x₀ x₁) (T : I) : Path (γ T) x₁ :=
{
  toFun := fun t => γ ⟨(σ T : ℝ) * ↑t + ↑T, interp_left_mem_I T t⟩,
  source' := by simp,
  target' := by simp [γ.target'],
}

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
lemma continuous_trans_reparam {T : I} (hT₀ : 0 < T) (hT₁ : T < 1) : Continuous (trans_reparam T) := by sorry

lemma trans_reparam_mem_I (t : I) {T : I} (hT₀ : 0 < T) (hT₁ : T < 1): trans_reparam T t ∈ I := by
  unfold trans_reparam
  split
  case inl h₀ => {
    constructor
    {
      exact div_nonneg t.2.1 (le_of_lt (unitIAux.double_pos_of_pos hT₀))
    }
    {
      apply (div_le_one (unitIAux.double_pos_of_pos hT₀)).mpr
      have : 0 < (T : ℝ) := hT₀
      have : (T : ℝ) ≤ (2 * T : ℝ) := by linarith only [this]
      apply le_trans h₀ this
    }
  }
  case inr h₀ => {
    constructor
    {
      apply div_nonneg _ (le_of_lt (unitIAux.double_sigma_pos_of_lt_one hT₁))
      -- linarith [unitIAux.double_sigma_pos_of_lt_one hT₁]
      sorry
    }
    {
      exact (div_le_one (unitIAux.double_sigma_pos_of_lt_one hT₁)).mpr (by
        linarith only [unitInterval.le_one t])
    }
  }

lemma trans_reparam_zero (T : I) : trans_reparam T 0 = 0 := by
  unfold trans_reparam
  simp
  intro hT
  linarith [unitInterval.nonneg T]

lemma trans_reparam_one {T : I} (hT₁ : T < 1): trans_reparam T 1 = 1 := sorry

lemma monotone_trans_reparam {T : I} (hT₀ : 0 < T) (hT₁ : T < 1) : Monotone (trans_reparam T) := sorry

lemma first_trans_second_reparam_eq_self_aux (γ : Path x₀ x₁) (t : I) {T: I} (hT₀ : 0 < T) (hT₁ : T < 1) :
  γ t = ((FirstPart γ T).trans (SecondPart γ T)).reparam
  (fun t => ⟨trans_reparam T t, trans_reparam_mem_I t hT₀ hT₁⟩)
  (by continuity)
  (Subtype.ext $ trans_reparam_zero T) (Subtype.ext $ trans_reparam_one hT₁) t := sorry

lemma first_trans_second_reparam_eq_self (γ : Path x₀ x₁) {T: I} (hT₀ : 0 < T) (hT₁ : T < 1) :
γ = ((FirstPart γ T).trans (SecondPart γ T)).reparam
  (fun t => ⟨trans_reparam T t, trans_reparam_mem_I t hT₀ hT₁⟩)
  (by continuity)
  (Subtype.ext $ trans_reparam_zero T) (Subtype.ext $ trans_reparam_one hT₁) := by
  ext t
  exact first_trans_second_reparam_eq_self_aux γ t hT₀ hT₁

end SplitPath

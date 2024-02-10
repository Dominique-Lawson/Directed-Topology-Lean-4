import Lean4.dipath
import Lean4.dTop
import Lean4.unit_interval_aux

/-
  This file contains definitions about stretching a (directed) path in `I` in two ways:
    If its image is contained in `[0, 1/2]`, it can be stretched upwards
    If its image is contained in `[1/2, 1]`, it can be stretched downwards

  These cases can be determined by the endpoints of the directed path.
-/

open unitIAux
open scoped unitInterval

namespace Dipath

/-### Stretching a path that only lives in the first half of the unit interval upwards -/

lemma double_mem_I_of_bounded {t₀ t₁ : I} (t : I) (γ : Dipath t₀ t₁) (ht₁ : ↑t₁ ≤ (2⁻¹ : ℝ)) : 2 * (γ t : ℝ) ∈ I :=
  double_mem_I $ le_trans (monotone_path_bounded γ.dipath_toPath t).2 (ht₁)

def stretch_up_path {t₀ t₁ : I} (γ : Dipath t₀ t₁) (ht₁ : ↑t₁ ≤ (2⁻¹ : ℝ)) : Path
  (⟨2 * ↑t₀, by { rw [←γ.source']; exact double_mem_I_of_bounded 0 γ ht₁ }⟩ : I)
  ⟨2 * ↑t₁, double_mem_I ht₁⟩ where
    toFun := fun t => ⟨2 * (γ t), double_mem_I_of_bounded t γ ht₁⟩
    source' := by simp [γ.source']
    target' := by simp [γ.target']

lemma isDipath_stretch_up {t₀ t₁ : I} (γ : Dipath t₀ t₁) (ht₁ : ↑t₁ ≤ (2⁻¹ : ℝ)) :
  IsDipath (stretch_up_path γ ht₁) := by
  intros x y hxy
  unfold stretch_up_path
  simp
  exact γ.dipath_toPath hxy

def stretch_up {t₀ t₁ : I} (γ : Dipath t₀ t₁) (ht₁ : ↑t₁ ≤ (2⁻¹ : ℝ)) : Dipath
  (⟨2 * ↑t₀, by { rw [←γ.source']; exact double_mem_I_of_bounded 0 γ ht₁ }⟩ : I)
  ⟨2 * ↑t₁, double_mem_I ht₁⟩ where
    toPath := stretch_up_path γ ht₁
    dipath_toPath := isDipath_stretch_up γ ht₁

/-### Stretching a path that only lives in the second half of the unit interval downwards -/

lemma double_sub_one_mem_I_of_bounded {t₀ t₁ : I} (t : I) (γ : Dipath t₀ t₁) (ht₀ : (2⁻¹ : ℝ) ≤ ↑t₀)
 : 2 * (γ t : ℝ) - 1 ∈ I :=
  double_sub_one_mem_I $ le_trans ht₀ (monotone_path_bounded γ.dipath_toPath t).1

def stretch_down_path {t₀ t₁ : I} (γ : Dipath t₀ t₁) (ht₀ : (2⁻¹ : ℝ) ≤ ↑t₀) : Path
  (⟨2 * ↑t₀ - 1, double_sub_one_mem_I ht₀⟩ : I)
  ⟨2 * ↑t₁ - 1, by { rw [←γ.target']; exact double_sub_one_mem_I_of_bounded 1 γ ht₀ }⟩ where
    toFun := fun t => ⟨2 * (γ t) - 1, double_sub_one_mem_I_of_bounded t γ ht₀⟩
    source' := by simp [γ.source']
    target' := by simp [γ.target']

lemma stretch_down_is_dipath {t₀ t₁ : I} (γ : Dipath t₀ t₁) (ht₀ : (2⁻¹ : ℝ) ≤ ↑t₀) :
  IsDipath (stretch_down_path γ ht₀) := by
  intros x y hxy
  unfold stretch_down_path
  simp
  exact γ.dipath_toPath hxy

def stretch_down {t₀ t₁ : I} (γ : Dipath t₀ t₁) (ht₀ : (2⁻¹ : ℝ) ≤ ↑t₀) : Dipath
  (⟨2 * ↑t₀ - 1, double_sub_one_mem_I ht₀⟩ : I)
  ⟨2 * ↑t₁ - 1, by { rw [←γ.target']; exact double_sub_one_mem_I_of_bounded 1 γ ht₀ }⟩ where
    toPath := stretch_down_path γ ht₀
    dipath_toPath := stretch_down_is_dipath γ ht₀

end Dipath

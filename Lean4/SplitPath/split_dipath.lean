import Lean4.SplitPath.split_path

noncomputable section
universe u
variable {X : Type u} [DirectedSpace X] {x₀ x₁ : X}

namespace SplitDipath

open SplitPath
open scoped unitInterval

lemma first_part_is_dipath {γ : Path x₀ x₁} (γ_dipath : IsDipath γ) {T : I} (hT₀ : 0 < T) :
  IsDipath (FirstPart γ T) := by

  let φ : Path 0 T := {
    toFun := fun t => ⟨(T : ℝ) * (t : ℝ), unitInterval.mul_mem T.2 t.2⟩
    source' := by simp
    target' := by simp
  }

  have : FirstPart γ T = (φ.map γ.continuous_toFun).cast γ.source.symm rfl := by { ext; rfl }
  rw [this]

  apply isDipath_cast _ γ.source.symm rfl
  exact isDipath_reparam (fun x y hxy => (mul_le_mul_left (Subtype.coe_lt_coe.mpr hT₀)).mpr hxy) γ_dipath


lemma second_part_is_dipath {γ : Path x₀ x₁} (γ_dipath : IsDipath γ) {T : I} (hT₁ : T < 1) :
  IsDipath (SecondPart γ T) := by
  let φ : Path T 1 := {
    toFun := fun t => ⟨(σ T : ℝ) * (t : ℝ) + (T : ℝ), interp_left_mem_I T t⟩
    source' := by simp
    target' := by simp
  }

  have : SecondPart γ T = ((φ.map γ.continuous_toFun).cast rfl γ.target.symm) := by { ext; rfl }
  rw [this]

  apply isDipath_cast _ rfl γ.target.symm
  apply isDipath_reparam _ γ_dipath
  intros x y hxy
  simp
  exact (mul_le_mul_left (sub_pos.mpr (Subtype.coe_lt_coe.mpr hT₁))).mpr hxy

def first_part_dipath (γ : Dipath x₀ x₁) {T : I} (hT₀ : 0 < T) : Dipath x₀ (γ T) := {
  FirstPart γ T with
  dipath_toPath := by exact first_part_is_dipath γ.dipath_toPath hT₀
}

def second_part_dipath (γ : Dipath x₀ x₁) {T : I} (hT₁ : T < 1) : Dipath (γ T) x₁ := {
  SecondPart γ T with
  dipath_toPath := by exact second_part_is_dipath γ.dipath_toPath hT₁
}

lemma first_part_apply (γ : Dipath x₀ x₁) {T : I} (hT₀ : 0 < T) (t : I) :
  (first_part_dipath γ hT₀) t = γ ⟨ T* t, unitInterval.mul_mem T.2 t.2⟩ := rfl
lemma second_part_apply (γ : Dipath x₀ x₁) {T : I} (hT₁ : T < 1) (t : I) :
  (second_part_dipath γ hT₁) t = γ ⟨(σ T : ℝ) * (t : ℝ) + (T : ℝ), interp_left_mem_I T t⟩ := rfl

def trans_reparam_map {T : I} (hT₀ : 0 < T) (hT₁ : T < 1) : D(I, I) :=
{
  toFun := fun t => ⟨trans_reparam T t, trans_reparam_mem_I t hT₀ hT₁⟩,
  directed_toFun := DirectedUnitInterval.directed_of_monotone _ (monotone_trans_reparam hT₀ hT₁)
}

lemma trans_reparam_map_zero {T : I} (hT₀ : 0 < T) (hT₁ : T < 1) : trans_reparam_map hT₀ hT₁ 0 = 0 :=
  Subtype.ext (trans_reparam_zero T)
lemma trans_reparam_map_one {T : I} (hT₀ : 0 < T) (hT₁ : T < 1) : trans_reparam_map hT₀ hT₁ 1 = 1 :=
  Subtype.ext (trans_reparam_one hT₁)

lemma first_trans_second_reparam_eq_self (γ : Dipath x₀ x₁) {T: I} (hT₀ : 0 < T) (hT₁ : T < 1) :
  γ = ((first_part_dipath γ hT₀).trans (second_part_dipath γ hT₁)).reparam
    (trans_reparam_map hT₀ hT₁) (trans_reparam_map_zero _ _) (trans_reparam_map_one _ _) := by
  ext t
  exact first_trans_second_reparam_eq_self_aux (γ : Path x₀ x₁) t hT₀ hT₁

end SplitDipath

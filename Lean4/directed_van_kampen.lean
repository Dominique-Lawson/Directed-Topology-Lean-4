import Mathlib.CategoryTheory.Limits.Shapes.CommSq
import Lean4.dihomotopy_cover
import Lean4.pushout_alternative
import Lean4.dihomotopy_to_path_dihomotopy
import Lean4.morphism_aux

/-
  This file contains the directed version of the Van Kampen Theorem.
  The statement is as follows:
  Let `X : dTopCat` and `X₁ X₂ : Set X` such that `X₁` and `X₂` are both open and `X₁ ∪ X₂ = X`.
  Let `i₁ : X₁ ∩ X₂ → X₁`, `i₂ : X₁ ∩ X₂ → X₂`, `j₁ : X₁ → X` and `j₂ : X₂ → X` be the inclusion maps in `dTopCat`.
  Then we have a pushout in `Cat`:
  dπₓ(X₁ ∩ X₂) ------ dπₘ i₁ -----> dπₓ(X₁)
       |                              |
       |                              |
       |                              |
     dπₘ i₂                         dπₘ j₁
       |                              |
       |                              |
       |                              |
    dπₓ(X₂) ------- dπₘ j₂ ------> dπₓ(X)

  The proof we give is constructive and is based on the proof given by
  Marco Grandis, Directed Homotopy Theory I, published in Cahiers de topologie et géométrie différentielle catégoriques, 44, no 4, pages 307-309, 2003.
-/

universe u v

open Set
open scoped unitInterval Classical FundamentalCategory

attribute [local instance] Dipath.Dihomotopic.setoid

noncomputable section

namespace DirectedVanKampen

open FundamentalCategory DiSubtype CategoryTheory

variable {X : dTopCat.{u}} {X₁ X₂ : Set X}
variable (hX : X₁ ∪ X₂ = Set.univ)
variable (X₁_open : IsOpen X₁) (X₂_open : IsOpen X₂)

-- We will use a shorthand notation for the 4 morphisms in dTop:
-- i₁ : X₁ ∩ X₂ ⟶ X₁
local notation "i₁" => dTopCat.DirectedSubsetHom $ (Set.inter_subset_left X₁ X₂)
-- i₁ : X₁ ∩ X₂ ⟶ X₂
local notation "i₂" => dTopCat.DirectedSubsetHom $ (Set.inter_subset_right X₁ X₂)
-- j₁ : X₁ ⟶ X
local notation "j₁" => dTopCat.DirectedSubtypeHom X₁
-- j₂ : X₂ ⟶ X
local notation "j₂" => dTopCat.DirectedSubtypeHom X₂

namespace PushoutFunctor

open Dipath Dipath.covered Dipath.covered_partwise

variable {x y : X} {C : CategoryTheory.Cat.{u, u}}
variable (F₁ : (dπₓ (dTopCat.of X₁) ⟶ C)) (F₂ : (dπₓ (dTopCat.of X₂) ⟶ C))
variable (h_comm : (dπₘ (dTopCat.DirectedSubsetHom $ (Set.inter_subset_left X₁ X₂))) ⋙ F₁ =
                  ((dπₘ (dTopCat.DirectedSubsetHom $ (Set.inter_subset_right X₁ X₂))) ⋙ F₂))

section FunctorProps

open CategoryTheory

variable {Y : dTopCat.{u}} {Y₀ : Set Y} {F : dπₓ (dTopCat.of Y₀) ⥤ C}

lemma subset_functor_trans {x y z : Y} {γ₁ : Dipath x y} {γ₂ : Dipath y z} (hγ : range (γ₁.trans γ₂) ⊆ Y₀) :
    (F.map ⟦SubtypeDipath γ₁ (subsets_of_trans_subset hγ).1⟧ ≫ F.map ⟦SubtypeDipath γ₂ (subsets_of_trans_subset hγ).2⟧) =
      F.map ⟦SubtypeDipath (γ₁.trans γ₂) hγ⟧ := by
  rw [←subtype_trans hγ, Dipath.Dihomotopic.comp_lift]
  exact (F.map_comp _ _).symm

lemma subset_functor_reparam {x y : Y} {γ : Dipath x y} (hγ : range γ ⊆ Y₀) {f : D(I, I)} (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
    F.map ⟦SubtypeDipath (γ.reparam f hf₀ hf₁)
        (show range (γ.reparam f hf₀ hf₁) ⊆ Y₀ by exact (Dipath.range_reparam γ f hf₀ hf₁).symm ▸ hγ)⟧ =
        F.map ⟦SubtypeDipath γ hγ⟧ := by
  congr 1
  rw [subtype_reparam hγ hf₀ hf₁]
  symm
  exact Quotient.eq.mpr (Dipath.Dihomotopic.reparam (SubtypeDipath γ hγ) f hf₀ hf₁)

lemma functor_cast {X : dTopCat} (F : (dπₓ X) ⥤ C) {x y x' y' : X} (γ : Dipath x y) (hx : x' = x) (hy : y' = y) :
    F.map ⟦γ.cast hx hy⟧ =
      (eqToHom (congrArg F.obj (congrArg FundamentalCategory.mk hx))) ≫ F.map ⟦γ⟧ ≫
      (eqToHom (congrArg F.obj (congrArg FundamentalCategory.mk hy)).symm) := by
  subst_vars
  simp
  congr 2

end FunctorProps

/-
  Given a category C and functors F₁ : dπₓ X₁ ⥤ C and F₂ : dπₓ X₂ ⥤ C, we will construct a functor F : dπₓ X ⥤ C
-/

/- ### Functor on Objects -/

/-
- Define the behaviour on objects
-/
def FunctorOnObj (x : dπₓ X) : C :=
  Or.by_cases
    ((Set.mem_union x.as X₁ X₂).mp (Filter.mem_top.mpr hX x.as))
      (fun hx => F₁.obj ⟨x.as, hx⟩)
      (fun hx => F₂.obj ⟨x.as, hx⟩)

-- We will use the shorhand notation F_obj
local notation "F_obj" => FunctorOnObj hX F₁ F₂

/-
  Under the assumption that the square commutes, we can show how the functor behaves on objects
-/

variable {F₁ F₂}

lemma functorOnObj_apply_one {x : X} (hx : x ∈ X₁) : F₁.obj ⟨x, hx⟩ = F_obj ⟨x⟩ := by
  -- TODO: This is unnecessary, but forces Lean to add the condition h_comm to functor_obj_apply_one. This keeps the symmetry
  have := h_comm
  convert (dif_pos hx).symm using 1
  rfl

lemma functorOnObj_apply_two {x : X} (hx₂ : x ∈ X₂) : F₂.obj ⟨x, hx₂⟩ = F_obj ⟨x⟩ := by
  by_cases hx₁ : x ∈ X₁
  case pos =>
    have hx₀ : x ∈ X₁ ∩ X₂ := ⟨hx₁, hx₂⟩
    have : F₁.obj ((dπₘ i₁).obj ⟨x, hx₀⟩) = F₂.obj ((dπₘ i₂).obj ⟨x, hx₀⟩) :=
      show ((dπₘ i₁) ⋙ F₁).obj ⟨x, hx₀⟩ = ((dπₘ i₂) ⋙ F₂).obj ⟨x, hx₀⟩ by rw [h_comm]

    have : F₁.obj ⟨x, hx₁⟩ = F₂.obj (⟨x, hx₂⟩) :=
      calc F₁.obj ⟨x, hx₁⟩
        _ = F₁.obj ((dπₘ i₁).obj ⟨x, hx₀⟩) := rfl
        _ = F₂.obj ((dπₘ i₂).obj ⟨x, hx₀⟩) := this
        _ = F₂.obj (⟨x, hx₂⟩) := rfl

    rw [this.symm]
    convert (dif_pos hx₁).symm using 1; rfl
  case neg =>
    convert (dif_neg hx₁).symm using 1; rfl

/- ### Functor on Maps -/

/-
  Define the mapping behaviour on paths that are fully covered by one set
-/
def FunctorOnHomOfCoveredAux₁ {γ : Dipath x y} (hγ : range γ ⊆ X₁) :
    F_obj ⟨x⟩ ⟶ F_obj ⟨y⟩ :=
  (eqToHom (functorOnObj_apply_one hX h_comm (source_elt_of_image_subset hγ)).symm) ≫
  (F₁.map ⟦SubtypeDipath γ hγ⟧) ≫
  (eqToHom (functorOnObj_apply_one hX h_comm (target_elt_of_image_subset hγ)))

def FunctorOnHomOfCoveredAux₂ {γ : Dipath x y} (hγ : range γ ⊆ X₂) :
    F_obj ⟨x⟩ ⟶ F_obj ⟨y⟩ :=
  (eqToHom (functorOnObj_apply_two hX h_comm (source_elt_of_image_subset hγ)).symm) ≫
  (F₂.map ⟦SubtypeDipath γ hγ⟧) ≫
  (eqToHom (functorOnObj_apply_two hX h_comm (target_elt_of_image_subset hγ)))

/-
  Show that these maps respect composition of paths
-/
lemma functorOnHomOfCoveredAux₁_trans {x y z : X} {γ₁ : Dipath x y} {γ₂ : Dipath y z} (hγ : range (γ₁.trans γ₂) ⊆ X₁) :
    FunctorOnHomOfCoveredAux₁ hX h_comm hγ =
      FunctorOnHomOfCoveredAux₁ hX h_comm (subsets_of_trans_subset hγ).1
      ≫ FunctorOnHomOfCoveredAux₁ hX h_comm (subsets_of_trans_subset hγ).2 := by
  unfold FunctorOnHomOfCoveredAux₁
  rw [(subset_functor_trans hγ).symm]
  simp

lemma functorOnHomOfCoveredAux₂_trans {x y z : X} {γ₁ : Dipath x y} {γ₂ : Dipath y z} (hγ : range (γ₁.trans γ₂) ⊆ X₂) :
    FunctorOnHomOfCoveredAux₂ hX h_comm hγ =
      FunctorOnHomOfCoveredAux₂ hX h_comm (subsets_of_trans_subset hγ).1
      ≫ FunctorOnHomOfCoveredAux₂ hX h_comm (subsets_of_trans_subset hγ).2 := by
  unfold FunctorOnHomOfCoveredAux₂
  rw [(subset_functor_trans hγ).symm]
  simp

/-
 Show that the maps respect reparametrization of paths
-/
lemma functorOnHomOfCoveredAux₁_reparam {x y : X} {γ : Dipath x y} (hγ : range γ ⊆ X₁)
  {f : D(I, I)} (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
    FunctorOnHomOfCoveredAux₁ hX h_comm hγ = FunctorOnHomOfCoveredAux₁ hX h_comm (reparam_subset_of_subset hγ hf₀ hf₁) := by
  unfold FunctorOnHomOfCoveredAux₁
  rw [subset_functor_reparam hγ hf₀ hf₁]

lemma functorOnHomOfCoveredAux₂_reparam {x y : X} {γ : Dipath x y} (hγ : range γ ⊆ X₂)
  {f : D(I, I)} (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
    FunctorOnHomOfCoveredAux₂ hX h_comm hγ = FunctorOnHomOfCoveredAux₂ hX h_comm (reparam_subset_of_subset hγ hf₀ hf₁) := by
  unfold FunctorOnHomOfCoveredAux₂
  rw [subset_functor_reparam hγ hf₀ hf₁]

/-
 Show that the maps respect reparametrization of paths
-/
lemma functorOnHomOfCoveredAux₁_refl {x : X} (hx : x ∈ X₁) :
  FunctorOnHomOfCoveredAux₁ hX h_comm (range_refl_subset_of_mem hx) = 𝟙 (F_obj ⟨x⟩) := by
  unfold FunctorOnHomOfCoveredAux₁
  rw [subtype_refl, ←id_eq_path_refl, F₁.map_id]
  simp

lemma functorOnHomOfCoveredAux₂_refl {x : X} (hx : x ∈ X₂) :
  FunctorOnHomOfCoveredAux₂ hX h_comm (range_refl_subset_of_mem hx) = 𝟙 (F_obj ⟨x⟩) := by
  unfold FunctorOnHomOfCoveredAux₂
  rw [subtype_refl, ←id_eq_path_refl, F₂.map_id]
  simp

/-
  Show that for any path living in X₁ ∩ X₂, it does not matter whether we apply the first or second map
-/
lemma functorOnHomOfCoveredAux_equal {γ : Dipath x y} (hγ₁ : range γ ⊆ X₁) (hγ₂ : range γ ⊆ X₂) :
    FunctorOnHomOfCoveredAux₁ hX h_comm hγ₁ = FunctorOnHomOfCoveredAux₂ hX h_comm hγ₂ := by
  unfold FunctorOnHomOfCoveredAux₁ FunctorOnHomOfCoveredAux₂
  have hγ₀ : range γ ⊆ X₁ ∩ X₂ := subset_inter hγ₁ hγ₂
  apply (eqToHom_comp_iff _ _ _).mpr
  apply (comp_eqToHom_iff _ _ _).mpr
  simp
  exact map_eq_map_of_eq h_comm ⟦SubtypeDipath γ hγ₀⟧

/-
- ### Define the mapping behaviour on covered paths
-/
def FunctorOnHomOfCovered {γ : Dipath x y} (hγ : covered hX γ) :
    F_obj ⟨x⟩ ⟶ F_obj ⟨y⟩ :=
  Or.by_cases hγ
    (fun hγ => FunctorOnHomOfCoveredAux₁ hX h_comm hγ)
    (fun hγ => FunctorOnHomOfCoveredAux₂ hX h_comm hγ)

local notation "F₀" => FunctorOnHomOfCovered hX h_comm

section FunctorOnHomOfCoveredProperties

lemma functorOnHomOfCovered_apply_left {γ : Dipath x y} (hγ : range γ ⊆ X₁) :
    F₀ (Or.inl hγ) = FunctorOnHomOfCoveredAux₁ hX h_comm hγ := dif_pos hγ

lemma functorOnHomOfCovered_apply_left' {γ : Dipath x y} (hγ : range γ ⊆ X₁) :
    F₀ (covered_partwise_of_covered 0 (Or.inl hγ)) = FunctorOnHomOfCoveredAux₁ hX h_comm hγ :=
  functorOnHomOfCovered_apply_left _ _ _

lemma functorOnHomOfCovered_apply_right {γ : Dipath x y} (hγ : range γ ⊆ X₂) :
    F₀ (Or.inr hγ) = FunctorOnHomOfCoveredAux₂ hX h_comm hγ := by
  by_cases hγ₁ : range γ ⊆ X₁
  · rw [functorOnHomOfCovered_apply_left hX h_comm hγ₁]
    exact functorOnHomOfCoveredAux_equal hX h_comm hγ₁ hγ
  · apply dif_neg hγ₁

lemma functorOnHomOfCovered_equal {γ₁ γ₂ : Dipath x y} (h : γ₁ = γ₂) (hγ₁ : covered hX γ₁) (hγ₂ : covered hX γ₂) :
    F₀ hγ₁ = F₀ hγ₂ := by subst_vars; rfl

lemma functorOnHomOfCovered_refl : F₀ (covered_refl x hX) = 𝟙 (F_obj ⟨x⟩) := by
  cases ((Set.mem_union x X₁ X₂).mp (Filter.mem_top.mpr hX x))
  case inl hx₁ =>
    rw [←functorOnHomOfCoveredAux₁_refl hX h_comm hx₁]
    exact functorOnHomOfCovered_apply_left hX h_comm (DiSubtype.range_refl_subset_of_mem hx₁)
  case inr hx₂ =>
    rw [←functorOnHomOfCoveredAux₂_refl hX h_comm hx₂]
    exact functorOnHomOfCovered_apply_right hX h_comm (DiSubtype.range_refl_subset_of_mem hx₂)

lemma functorOnHomOfCovered_apply_right' {γ : Dipath x y} (hγ : range γ ⊆ X₂) :
    F₀ (covered_partwise_of_covered 0 (Or.inr hγ)) = FunctorOnHomOfCoveredAux₂ hX h_comm hγ :=
  functorOnHomOfCovered_apply_right _ _ _

lemma functorOnHomOfCovered_trans {x y z : X} {γ₁ : Dipath x y} {γ₂ : Dipath y z} (hγ : covered hX (γ₁.trans γ₂)) :
    F₀ hγ = (F₀ (covered_of_covered_trans hγ).1) ≫ (F₀ (covered_of_covered_trans hγ).2) := by
  cases hγ
  case inl hγ => -- γ is covered by X₁
    rw [functorOnHomOfCovered_apply_left _ _ hγ]
    rw [functorOnHomOfCoveredAux₁_trans]
    congr
    · exact (functorOnHomOfCovered_apply_left _ _ _).symm
    · exact (functorOnHomOfCovered_apply_left _ _ _).symm
  case inr hγ => -- γ is covered by X₂
    rw [functorOnHomOfCovered_apply_right _ _ hγ]
    rw [functorOnHomOfCoveredAux₂_trans]
    congr
    exact (functorOnHomOfCovered_apply_right _ _ (subsets_of_trans_subset hγ).1).symm
    exact (functorOnHomOfCovered_apply_right _ _ (subsets_of_trans_subset hγ).2).symm

lemma functorOnHomOfCovered_reparam {x y : X} {γ : Dipath x y} (hγ : covered hX γ)
  {f : D(I, I)} (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
    F₀ hγ = F₀ ((covered_reparam_iff γ hX f hf₀ hf₁).mp hγ) := by
  cases hγ
  case inl hγ =>
    have : range (γ.reparam f hf₀ hf₁) ⊆ X₁ := by rw [Dipath.range_reparam γ f hf₀ hf₁]; exact hγ
    rw [functorOnHomOfCovered_apply_left]
    rw [functorOnHomOfCoveredAux₁_reparam hX h_comm hγ hf₀ hf₁]
    rw [←functorOnHomOfCovered_apply_left hX h_comm this]
  case inr hγ =>
    have : range (γ.reparam f hf₀ hf₁) ⊆ X₂ := by rw [Dipath.range_reparam γ f hf₀ hf₁]; exact hγ
    rw [functorOnHomOfCovered_apply_right]
    rw [functorOnHomOfCoveredAux₂_reparam hX h_comm hγ hf₀ hf₁]
    rw [←functorOnHomOfCovered_apply_right hX h_comm this]

lemma functorOnHomOfCovered_cast {x y x' y' : X} {γ : Dipath x y} (hγ : covered hX γ) (hx : x' = x) (hy : y' = y) :
    F₀ ((covered_cast_iff γ hX hx hy).mp hγ) = (eqToHom (show F_obj ⟨x'⟩ = F_obj ⟨x⟩ by rw [hx])) ≫
      (F₀ hγ) ≫ (eqToHom (show F_obj ⟨y⟩ = F_obj ⟨y'⟩ by rw [hy])) := by
  subst_vars
  rw [eqToHom_refl, eqToHom_refl, Category.comp_id, Category.id_comp]

lemma functorOnHomOfCovered_cast_left {x y x' : X} {γ : Dipath x y} (hγ : covered hX γ) (hx : x' = x) :
    F₀ ((covered_cast_iff γ hX hx rfl).mp hγ) =
      (eqToHom (show F_obj ⟨x'⟩ = F_obj ⟨x⟩ by rw [hx])) ≫ (F₀ hγ) := by
  subst_vars
  rw [eqToHom_refl, Category.id_comp]

lemma functorOnHomOfCovered_cast_right {x y y' : X} {γ : Dipath x y} (hγ : covered hX γ) (hy : y' = y) :
  F₀ ((covered_cast_iff γ hX rfl hy).mp hγ) =
    (F₀ hγ) ≫ (eqToHom (show F_obj ⟨y⟩ = F_obj ⟨y'⟩ by rw [hy])) := by
  subst_vars
  rw [eqToHom_refl, Category.comp_id]

lemma functorOnHomOfCovered_split_comp {x y : X} {γ : Dipath x y} (hγ : covered hX γ) {T : I} (hT₀ : 0 < T) (hT₁ : T < 1) :
    F₀ hγ = (F₀ (covered_split_path hT₀ hT₁ hγ).1) ≫ (F₀ (covered_split_path hT₀ hT₁ hγ).2) := by
  have : covered hX ((SplitDipath.FirstPartDipath γ T).trans (SplitDipath.SecondPartDipath γ T)) := by
    rw [SplitDipath.first_trans_second_reparam_eq_self γ hT₀ hT₁] at hγ
    exact (covered_reparam_iff _ hX _ _ _).mpr hγ

  rw [←functorOnHomOfCovered_trans hX h_comm this]
  rw [functorOnHomOfCovered_reparam hX h_comm this
      (SplitDipath.trans_reparam_map_zero hT₀ hT₁)
      (SplitDipath.trans_reparam_map_one hT₀ hT₁)]
  congr
  apply SplitDipath.first_trans_second_reparam_eq_self

lemma functorOnHomOfCovered_dihomotopic {x y : X} {γ γ' : Dipath x y} {F : Dihomotopy γ γ'}
  (hF : Dipath.Dihomotopy.covered hX F) :
    F₀ (Dipath.Dihomotopy.covered_left_of_covered hF) = F₀ (Dipath.Dihomotopy.covered_right_of_covered hF) := by
  cases hF
  case inl hF =>
    have hγ := subset_trans (Dipath.Dihomotopy.range_left_subset F) hF
    have hγ' := subset_trans (Dipath.Dihomotopy.range_right_subset F) hF
    rw [functorOnHomOfCovered_equal hX h_comm rfl _ (Or.inl hγ)]
    rw [functorOnHomOfCovered_equal hX h_comm rfl _ (Or.inl hγ')]
    rw [functorOnHomOfCovered_apply_left hX h_comm hγ]
    rw [functorOnHomOfCovered_apply_left hX h_comm hγ']
    unfold FunctorOnHomOfCoveredAux₁
    rw [dihomSubtype_of_dihom_range_subset hγ hγ' hF]
  case inr hF =>
    have hγ := subset_trans (Dipath.Dihomotopy.range_left_subset F) hF
    have hγ' := subset_trans (Dipath.Dihomotopy.range_right_subset F) hF
    rw [functorOnHomOfCovered_equal hX h_comm rfl _ (Or.inr hγ)]
    rw [functorOnHomOfCovered_equal hX h_comm rfl _ (Or.inr hγ')]
    rw [functorOnHomOfCovered_apply_right hX h_comm hγ]
    rw [functorOnHomOfCovered_apply_right hX h_comm hγ']
    unfold FunctorOnHomOfCoveredAux₂
    rw [dihomSubtype_of_dihom_range_subset hγ hγ' hF]

end FunctorOnHomOfCoveredProperties

/-
-  ### Define the behaviour on partwise covered paths
-/

-- TODO: This definition now has (x y γ) instead of {x y γ} forcing an auxiliary function.
def FunctorOnHomOfCoveredPartwiseAux {n : ℕ} :
    ∀ (x y : X) (γ : Dipath x y) (_ : covered_partwise hX γ n), F_obj ⟨x⟩ ⟶ F_obj ⟨y⟩ :=
  Nat.recOn n
    (fun _ _ _ hγ => F₀ hγ)
    (fun _ ih _ _ _ hγ => (F₀ hγ.1) ≫ (ih _ _ _ hγ.2))

abbrev FunctorOnHomOfCoveredPartwise {n : ℕ} {x y : X} {γ : Dipath x y} (hγ : covered_partwise hX γ n) :=
  FunctorOnHomOfCoveredPartwiseAux hX h_comm x y γ hγ

local notation "Fₙ" => FunctorOnHomOfCoveredPartwise hX h_comm

lemma functorOnHomOfCoveredPartwise_apply_0 {x y : X} {γ : Dipath x y} (hγ : covered_partwise hX γ 0) :
    Fₙ hγ = F₀ hγ := rfl

lemma functorOnHomOfCoveredPartwise_apply_succ {n : ℕ} {x y : X} {γ : Dipath x y} (hγ : covered_partwise hX γ n.succ) :
    Fₙ hγ = (F₀ hγ.left) ≫ (Fₙ hγ.right) := rfl

lemma functorOnHomOfCoveredPartwise_equal {n : ℕ} {γ₁ γ₂ : Dipath x y} (h : γ₁ = γ₂)
  (hγ₁ : covered_partwise hX γ₁ n) (hγ₂ : covered_partwise hX γ₂ n) :
    Fₙ hγ₁ = Fₙ hγ₂ := by subst_vars; rfl

lemma functorOnHomOfCoveredPartwise_equal' {n m : ℕ} {γ₁ γ₂ : Dipath x y} (h₁ : γ₁ = γ₂)
  (h₂ : n = m) (hγ₁ : covered_partwise hX γ₁ n) (hγ₂ : covered_partwise hX γ₂ m) :
    Fₙ hγ₁ = Fₙ hγ₂ := by subst_vars; rfl

lemma functorOnHomOfCoveredPartwise_cast_params {n m : ℕ} {γ₁ γ₂ : Dipath x y} (h₁ : γ₁ = γ₂)
  (h₂ : n = m) (hγ₁ : covered_partwise hX γ₁ n) :
    Fₙ hγ₁ = Fₙ (covered_partwise_of_equal hX h₁ h₂ hγ₁) := by subst_vars; rfl

lemma functorOnHomOfCoveredPartwise_cast {x y x' y' : X} {n : ℕ} {γ : Dipath x y}
  (hγ : covered_partwise hX γ n) (hx : x' = x) (hy : y' = y) :
    Fₙ ((covered_partwise_cast_iff hX γ hx hy).mp hγ) =
      (eqToHom (by rw [hx])) ≫ (Fₙ hγ) ≫ (eqToHom (by rw [hy])) := by
  subst_vars
  rw [eqToHom_refl, eqToHom_refl, Category.comp_id, Category.id_comp]
  apply functorOnHomOfCoveredPartwise_equal
  rfl

lemma functorOnHomOfCoveredPartwise_cast_left {x y x' : X} {n : ℕ} {γ : Dipath x y}
  (hγ : covered_partwise hX γ n) (hx : x' = x) :
    Fₙ ((covered_partwise_cast_iff hX γ hx rfl).mp hγ) = (eqToHom (by rw [hx])) ≫ (Fₙ hγ) := by
  subst_vars
  rw [eqToHom_refl, Category.id_comp]
  apply functorOnHomOfCoveredPartwise_equal
  rfl

lemma functorOnHomOfCoveredPartwise_cast_right {x y y' : X} {n : ℕ} {γ : Dipath x y} (hγ : covered_partwise hX γ n) (hy : y' = y) :
    Fₙ ((covered_partwise_cast_iff hX γ rfl hy).mp hγ) = (Fₙ hγ) ≫ (eqToHom (by rw [hy])) := by
  subst_vars
  rw [eqToHom_refl, Category.comp_id]
  apply functorOnHomOfCoveredPartwise_equal
  rfl

lemma functorOnHomOfCoveredPartwise_refine_of_covered (k : ℕ):
  Π {x y : X} {γ : Dipath x y} (hγ : covered hX γ),
    Fₙ (covered_partwise_of_covered 0 hγ) = Fₙ (covered_partwise_of_covered k hγ) := by
  induction k
  case zero =>
    intro x y γ hγ
    rfl
  case succ k ih =>
    intro x y γ hγ
    rw [functorOnHomOfCoveredPartwise_apply_succ hX h_comm (covered_partwise_of_covered k.succ hγ)]
    show (FunctorOnHomOfCovered hX h_comm hγ) = _
    have : 1 < k + 2 := by linarith
    rw [functorOnHomOfCovered_split_comp hX h_comm hγ (Fraction.ofPos_pos (lt_trans zero_lt_one this)) (Fraction.ofPos_lt_one this)]
    congr
    apply ih
    exact (covered_split_path (Fraction.ofPos_pos (lt_trans zero_lt_one this)) (Fraction.ofPos_lt_one this) hγ).2

/--
  When a path is partwise covered by n+1 paths, you can apply Fₙ to both parts of γ, when restricting to
  [0, (d+1)/(n+1)] and [(d+1)/(n+1)]. This lemma states that the composition of these two gives Fₙ γ
-/
lemma functorOnHomOfCoveredPartwise_split {n : ℕ} :
    Π {d : ℕ} (hdn : n > d) {x y : X} {γ : Dipath x y} (hγ : covered_partwise hX γ n),
    Fₙ hγ = Fₙ (covered_partwise_first_part_d hX (Nat.succ_lt_succ hdn) hγ) ≫
          Fₙ (covered_partwise_second_part_d hX (Nat.succ_lt_succ hdn) hγ) := by
  induction n
  case zero =>
    intro d hd
    linarith
  case succ n ih_n =>
    intro d hdn
    induction d
    case zero =>
        intro x y γ hγ
        rfl
    case succ d _ =>
      intro x y γ hγ
      rw [functorOnHomOfCoveredPartwise_apply_succ hX h_comm hγ]
      have : n > d := Nat.succ_lt_succ_iff.mp hdn
      rw [ih_n this _]
      rw [functorOnHomOfCoveredPartwise_apply_succ hX h_comm _]
      rw [Category.assoc]
      show F₀ _ ≫ (Fₙ _ ≫ Fₙ _) =  F₀ _ ≫ (Fₙ _ ≫ Fₙ _)
      apply eq_of_morphism
      · apply (comp_eqToHom_iff _ _ _).mp
        rw [←functorOnHomOfCovered_cast_right]
        apply functorOnHomOfCovered_equal
        rw [SplitProperties.firstPart_of_firstPart γ (Nat.succ_lt_succ hdn) (Nat.succ_pos d.succ)]
      · rw [←Category.assoc]
        apply eq_of_morphism
        · apply (comp_eqToHom_iff _ _ _).mp
          apply (eqToHom_comp_iff _ _ _).mp
          rw [←functorOnHomOfCoveredPartwise_cast]
          apply functorOnHomOfCoveredPartwise_equal
          rw [SplitProperties.first_part_of_second_part γ (hdn) (Nat.succ_pos d)]
        · rw [←functorOnHomOfCoveredPartwise_cast_left]
          apply functorOnHomOfCoveredPartwise_equal'
          rw [SplitProperties.second_part_of_second_part γ (Nat.lt_of_succ_lt_succ hdn)]
          rw [Nat.succ_sub_succ]

/--
  If a path can be covered partwise by `(n+1) ≥ 2` parts, its refinement by covering it by `k*(n+1)` parts is equal to the composition
  of covering the first part in `k` parts and the second part in `k*n` parts.
-/
lemma functorOnHomOfCoveredPartwise_refine_apply (n k : ℕ) {x y : X} {γ : Dipath x y} (hγ : covered_partwise hX γ n.succ) :
    Fₙ (covered_partwise_refine hX n.succ k hγ) =
      (Fₙ $ covered_partwise_of_covered k hγ.left) ≫ (Fₙ $ covered_partwise_refine hX n k hγ.right) := by
  have h₀ : k + 1 < (n+1+1) * (k + 1) := by
    have : n + 1 + 1 > 1 := by linarith
    convert Nat.mul_lt_mul_of_pos_right (this) (Nat.succ_pos k) using 1
    exact (one_mul k.succ).symm

  have h₁ : (n+1+1)*(k+1) - 1 > (k + 1) - 1 := Nat.pred_lt_pred (ne_of_gt (Nat.succ_pos k)) h₀
  have h₂ := Fraction.eq_inv₁ (Nat.succ_pos k) (le_of_lt (Nat.succ_lt_succ h₁))
  rw [functorOnHomOfCoveredPartwise_split hX h_comm h₁ (covered_partwise_refine hX n.succ k hγ)]

  apply eq_of_morphism
  · rw [←functorOnHomOfCoveredPartwise_cast_right hX h_comm _ (congr_arg γ h₂.symm)]
    apply functorOnHomOfCoveredPartwise_equal hX h_comm
    ext t
    rw [Dipath.cast_apply]
    exact SplitProperties.firstPart_eq_of_point_eq _ h₂.symm _
  · rw [←functorOnHomOfCoveredPartwise_cast_left hX h_comm _ (congr_arg γ h₂.symm)]
    apply functorOnHomOfCoveredPartwise_equal' hX h_comm
    ext t
    rw [Dipath.cast_apply]
    exact SplitProperties.secondPart_eq_of_point_eq _ h₂.symm _
    simp
    rw [Nat.succ_mul, Nat.sub_right_comm, Nat.add_sub_cancel]

lemma functorOnHomOfCoveredPartwise_refine {n : ℕ} (k : ℕ) :
    Π {x y : X} {γ : Dipath x y} (hγ_n : covered_partwise hX γ n),
      Fₙ hγ_n = Fₙ (covered_partwise_refine hX n k hγ_n) := by
  induction n
  case zero => apply functorOnHomOfCoveredPartwise_refine_of_covered
  case succ n ih =>
    intros x y γ hγ
    rw [functorOnHomOfCoveredPartwise_refine_apply hX h_comm n k hγ]
    rw [← functorOnHomOfCoveredPartwise_refine_of_covered hX h_comm _ hγ.left]
    rw [functorOnHomOfCoveredPartwise_apply_succ hX h_comm hγ]
    rw [ih hγ.right]
    rfl

lemma functorOnHomOfCoveredPartwise_apply_right_side {x y : X} {γ : Dipath x y} {n : ℕ} (hγ : covered_partwise hX γ n.succ) :
    Fₙ hγ = Fₙ (covered_partwise_first_part_end_split hX hγ) ≫
            F₀ (covered_second_part_end_split hX hγ) := by
  rw [functorOnHomOfCoveredPartwise_split hX h_comm (Nat.lt_succ_self n)]
  rw [functorOnHomOfCoveredPartwise_equal' hX h_comm rfl (Nat.sub_self n.succ)]
  rw [functorOnHomOfCoveredPartwise_apply_0]

lemma functorOnHomOfCoveredPartwise_trans_case_0 {x y z : X} {γ₁ : Dipath x y} {γ₂ : Dipath y z}
  (hγ₁ : covered_partwise hX γ₁ 0) (hγ₂ : covered_partwise hX γ₂ 0) :
    Fₙ (covered_partwise_trans hγ₁ hγ₂) = (Fₙ hγ₁) ≫ (Fₙ hγ₂) := by
  rw [functorOnHomOfCoveredPartwise_apply_0]
  rw [functorOnHomOfCoveredPartwise_apply_0]
  rw [functorOnHomOfCoveredPartwise_apply_succ]
  rw [functorOnHomOfCoveredPartwise_apply_0]
  rw [functorOnHomOfCovered_equal hX h_comm (SplitProperties.first_part_trans γ₁ γ₂) _ ((covered_cast_iff γ₁ hX _ _).mp hγ₁)]
  rw [functorOnHomOfCovered_equal hX h_comm (SplitProperties.second_part_trans γ₁ γ₂) _ ((covered_cast_iff γ₂ hX _ _).mp hγ₂)]
  rw [functorOnHomOfCovered_cast_right hX h_comm hγ₁]
  rw [functorOnHomOfCovered_cast_left hX h_comm hγ₂]
  simp

lemma functorOnHomOfCoveredPartwise_trans {n : ℕ} :
    Π {x y z : X} {γ₁ : Dipath x y} {γ₂ : Dipath y z} (hγ₁ : covered_partwise hX γ₁ n) (hγ₂ : covered_partwise hX γ₂ n),
      Fₙ (covered_partwise_trans hγ₁ hγ₂) = (Fₙ hγ₁) ≫ (Fₙ hγ₂) := by
  induction n
  case zero =>
    intro x y z γ₁ γ₂ hγ₁ hγ₂
    exact functorOnHomOfCoveredPartwise_trans_case_0 hX h_comm hγ₁ hγ₂
  case succ n ih =>
    intros x y z γ₁ γ₂ hγ₁ hγ₂
    rw [functorOnHomOfCoveredPartwise_apply_succ hX h_comm]
    rw [functorOnHomOfCoveredPartwise_apply_succ hX h_comm hγ₁]
    rw [Category.assoc]
    apply eq_of_morphism
    · rw [←functorOnHomOfCovered_cast_right]
      apply functorOnHomOfCovered_equal
      ext t
      rw [Dipath.cast_apply]
      exact SplitProperties.trans_first_part γ₁ γ₂ n.succ t
      exact SplitProperties.trans_image_inv_eq_first γ₁ γ₂ n.succ
    · rw [functorOnHomOfCoveredPartwise_apply_right_side hX h_comm hγ₂]
      rw [functorOnHomOfCoveredPartwise_cast_params hX h_comm rfl (Nat.pred_succ n)]
      rw [←Category.assoc (Fₙ _) _ _]
      rw [←ih _ _]
      have : (n.succ + n.succ).succ - 1 = (n + n).succ.succ := by
        rw [Nat.sub_one]
        rw [Nat.pred_succ (n.succ + n.succ)]
        rw [Nat.succ_add]
        rw [Nat.add_succ]
      rw [functorOnHomOfCoveredPartwise_cast_params hX h_comm rfl this]
      rw [←Category.assoc _ _]
      rw [←functorOnHomOfCoveredPartwise_cast_left]
      rw [functorOnHomOfCoveredPartwise_apply_right_side hX h_comm _]
      apply eq_of_morphism
      · rw [←functorOnHomOfCoveredPartwise_cast_right]
        apply functorOnHomOfCoveredPartwise_equal' hX h_comm _ rfl
        pick_goal 3
        ext t
        rw [Dipath.cast_apply]
        rw [Dipath.cast_apply]
        sorry
        sorry
        sorry
        -- exact SplitProperties.trans_first_part_of_second_part γ₁ γ₂ n t
        -- exact SplitProperties.second_part_trans_image_inv_eq_second γ₁ γ₂ n
      · rw [←functorOnHomOfCovered_cast_left]
        apply functorOnHomOfCovered_equal
        ext t
        rw [Dipath.cast_apply]
        exact SplitProperties.trans_second_part_second_part γ₁ γ₂ n t
        exact SplitProperties.second_part_trans_image_inv_eq_second γ₁ γ₂ n
      -- exact SplitProperties.trans_image_inv_eq_first γ₁ γ₂ n.succ

lemma functorOnHomOfCoveredPartwise_unique {n m : ℕ} {γ : Dipath x y}
  (hγ_n : covered_partwise hX γ n) (hγ_m : covered_partwise hX γ m) :
    Fₙ hγ_n = Fₙ hγ_m := by
  rw [functorOnHomOfCoveredPartwise_refine hX h_comm m hγ_n]
  rw [functorOnHomOfCoveredPartwise_refine hX h_comm n hγ_m]
  congr 2
  exact mul_comm _ _

end PushoutFunctor
end DirectedVanKampen

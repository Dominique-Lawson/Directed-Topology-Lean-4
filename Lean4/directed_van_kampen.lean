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

lemma functor_obj_apply_one {x : X} (hx : x ∈ X₁) : F₁.obj ⟨x, hx⟩ = F_obj ⟨x⟩ := by
  -- TODO: This is unnecessary, but forces Lean to add the condition h_comm to functor_obj_apply_one. This keeps the symmetry
  have := h_comm
  convert (dif_pos hx).symm using 1
  rfl

lemma functor_obj_apply_two {x : X} (hx₂ : x ∈ X₂) : F₂.obj ⟨x, hx₂⟩ = F_obj ⟨x⟩ := by
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
  (eqToHom (functor_obj_apply_one hX h_comm (source_elt_of_image_subset hγ)).symm) ≫
  (F₁.map ⟦SubtypeDipath γ hγ⟧) ≫
  (eqToHom (functor_obj_apply_one hX h_comm (target_elt_of_image_subset hγ)))

def FunctorOnHomOfCoveredAux₂ {γ : Dipath x y} (hγ : range γ ⊆ X₂) :
    F_obj ⟨x⟩ ⟶ F_obj ⟨y⟩ :=
  (eqToHom (functor_obj_apply_two hX h_comm (source_elt_of_image_subset hγ)).symm) ≫
  (F₂.map ⟦SubtypeDipath γ hγ⟧) ≫
  (eqToHom (functor_obj_apply_two hX h_comm (target_elt_of_image_subset hγ)))

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


end PushoutFunctor

end DirectedVanKampen

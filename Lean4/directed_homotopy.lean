import Lean4.SplitPath.split_dipath
import Lean4.stretch_path

/-
  This file contains the definitions of three type of directed homotopies:
  * `Dihomotopy f g` : the type of homotopies between two directed maps `f g : D(X, Y)`.
  * `Dihomotopy_with f g P` : the type of homotopies between two directed maps `f g : D(X, Y)` satisfying `P : D(X, Y) → Prop` at all intermediate point `t : I`.
  * `Dihomotopy_rel f g S` : the type of homotopies between two directed maps `f g : D(X, Y)` that are fixed on all points of `S : set X`.

  The structure of this file is based on the undirected variant, found at:
  https://github.com/leanprover-community/mathlib/blob/master/src/topology/homotopy/basic.lean
-/

namespace DirectedMap

open DirectedMap DirectedUnitInterval
open scoped unitInterval

noncomputable section

universe u v w

variable {X : Type u} {Y : Type v} {Z : Type w}
variable [DirectedSpace X] [DirectedSpace Y] [DirectedSpace Z]

/-- `DirectedMap.Dihomotopy f₀ f₁` is the type of directed homotopies from `f₀` to `f₁`. -/
structure Dihomotopy (f₀ f₁ : DirectedMap X Y) extends D((I × X), Y) :=
  (map_zero_left : ∀ x, toFun (0, x) = f₀.toFun x)
  (map_one_left : ∀ x, toFun (1, x) = f₁.toFun x)

section

-- TODO: Structure is different from how a Homotopy is defined in MathLib4: is that a problem?
/-- `DirectedMap.DihomotopyLike F f₀ f₁` states that `F` is a type of homotopies between `f₀` and `f₁` -/
class DihomotopyLike {X Y : outParam (Type*)} [DirectedSpace X] [DirectedSpace Y]
    (F : Type*) (f₀ f₁ : outParam <| D(X, Y)) [DirectedMapClass F (I × X) Y]
    extends DirectedMapClass F (I × X) Y where
  map_zero_left (f : F) : ∀ x, f (0, x) = f₀ x
  map_one_left (f : F) : ∀x, f (1, x) = f₁ x

end

namespace Dihomotopy

section

variables {f₀ f₁ : D(X, Y)}

instance : dihomotopy_class (dihomotopy f₀ f₁) f₀ f₁ :=
{ coe := λ f, f.to_fun,
  coe_injective' := λ f g h, by { obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f, obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g, congr' },
  map_continuous := λ f, f.continuous_to_fun,
  map_directed := λ f, f.directed_to_fun,
  map_zero_left := λ f, f.map_zero_left',
  map_one_left := λ f, f.map_one_left'
}

end

variables {f₀ f₁ : D(X, Y)}

/-- Helper instance for when there's too many metavariables to apply
`fun_like.has_coe_to_fun` directly. -/
instance : has_coe_to_fun (dihomotopy f₀ f₁) (λ _, I × X → Y) := fun_like.has_coe_to_fun

@[simp] lemma to_fun_eq_coe {f : dihomotopy f₀ f₁} : f.to_fun = (f : I × X → Y) := rfl

@[ext] theorem ext {f g : dihomotopy f₀ f₁} (h : ∀ x, f x = g x) : f = g := fun_like.ext f g h

def simps.apply (F : dihomotopy f₀ f₁) : I × X → Y := F

@[simp] lemma apply_zero (F : dihomotopy f₀ f₁) (a : X) : F (0, a) = f₀ a := F.map_zero_left' a
@[simp] lemma apply_one (F : dihomotopy f₀ f₁) (a : X) : F (1, a) = f₁ a := F.map_one_left' a
@[simp] lemma coe_to_continuous_map (F : dihomotopy f₀ f₁) : ⇑F.to_continuous_map = F := rfl
@[simp] lemma coe_to_directed_map (F : dihomotopy f₀ f₁) : ⇑F.to_directed_map = F := rfl

/--
Currying a dihomotopy to a map fron `I` to `D(X, Y)`.
-/
def curry (F : dihomotopy f₀ f₁) : I → D(X, Y) := begin
  intro t,
  exact directed_map.prod_const_fst ↑F t,
end

@[simp]
lemma curry_apply (F : dihomotopy f₀ f₁) (t : I) (x : X) : F.curry t x = F (t, x) := rfl

/--
Currying a dihomotopy to a map fron `X` to `D(I, Y)`.
-/
def curry_snd (F : dihomotopy f₀ f₁) : X → D(I, Y) := begin
  intro x,
  exact directed_map.prod_const_snd ↑F x,
end

@[simp]
lemma curry_snd_apply (F : dihomotopy f₀ f₁) (x : X) (t : I) : F.curry_snd x t = F (t, x) := rfl

def hom_to_dihom (F : continuous_map.homotopy (↑f₀ : C(X, Y)) ↑f₁) (HF : directed ↑F) : dihomotopy f₀ f₁ :=
{
  to_fun := F.to_fun,
  continuous_to_fun := F.continuous_to_fun,
  directed_to_fun := HF,
  map_zero_left' := F.map_zero_left',
  map_one_left' := F.map_one_left',
}

def dihom_to_hom (F : dihomotopy f₀ f₁) : continuous_map.homotopy ↑f₀ ↑f₁:=
{
  to_fun := F.to_fun,
  continuous_to_fun := F.continuous_to_fun,
  map_zero_left' := F.map_zero_left',
  map_one_left' := F.map_one_left',
}

instance coe_dihom_to_hom : has_coe (dihomotopy f₀ f₁) (continuous_map.homotopy ↑f₀ ↑f₁) := ⟨λ F, F.dihom_to_hom⟩

section

/-! Evaluating dihomotopies at intermidiate points -/

/--
Evaluating a dipath homotopy at an intermediate point in the left coordinate, giving us a `dipath`.
-/
def eval_at_left {X : dTop} {f g : D(I, X)} (F : dihomotopy f g) (t : I) : dipath (F (t, 0)) (F (t, 1)) :=
{
  to_fun := F.curry t,
  source' := by simp,
  target' := by simp,
  dipath_to_path := directed_unit_interval.is_dipath_of_is_dipath_comp_id
    $ (F.curry t).directed_to_fun directed_unit_interval.identity_path directed_unit_interval.identity_dipath,
}

/--
Given a dihomotopy H: f ∼ g, get the dipath traced by the point `x` as it moves from
`f x` to `g x`
-/
def eval_at_right {X : Type*} {Y : Type*} [directed_space X] [directed_space Y] {f g : D(X, Y)}
  (H : directed_map.dihomotopy f g) (x : X) : dipath (f x) (g x) :=
{ to_fun := λ t, H (t, x),
  source' := H.apply_zero x,
  target' := H.apply_one x,
  dipath_to_path :=
    begin
      convert H.directed_to_fun { to_fun := λ t, (t, x), source' := rfl, target' := rfl}
        ⟨directed_unit_interval.identity_dipath, is_dipath_constant _⟩; simp,
    end
}

end

/--
Given a directed map `f`, we can define a `dihomotopy f f` by `F (t, x) = f x`
-/
lemma directed_refl (f : D(X, Y)) : directed (↑(continuous_map.homotopy.refl (↑f : C(X, Y))) : C(I × X, Y)) :=
  λ ⟨t₀, x₀⟩ ⟨t₁, x₁⟩ γ γ_dipath, (f.directed_to_fun (γ.map continuous_snd) (directed_snd.directed_to_fun γ γ_dipath))

@[simps]
def refl (f : D(X, Y)) : dihomotopy f f := hom_to_dihom (continuous_map.homotopy.refl ↑f) (directed_refl f)

instance : inhabited (dihomotopy (directed_map.id X) (directed_map.id X)) := ⟨dihomotopy.refl _⟩

/- Note: there is no `dihomotopy.symm`, as paths generally cannot be reversed -/

/- Auxiliary functions to prove that continuous.homotopy.trans is directed if the given homotopies are directed -/
section trans_aux

section trans_aux₁

open split_path split_dipath

variables {t₀ t₁ : I} (γ : dipath t₀ t₁) {T : I} (hT₀ : 0 < T) (hT₁ : T < 1)
variables (ht₀ : (t₀ : ℝ) ≤ 2⁻¹) (ht₁ : 2⁻¹ ≤ (t₁ : ℝ)) (hT : γ T = half_I)
include hT₀ hT₁ hT

def first_part_stretch :
  dipath (⟨2 * (t₀.1 : ℝ), double_mem_I ht₀⟩ : I) 1 :=
{
  to_fun := λ t, dipath.stretch_up (first_part_dipath γ hT₀) (by { convert le_refl (2⁻¹ : ℝ), simp [hT], refl, }) t,
  source' := by simp,
  target' := by {
    simp [hT],
    apply subtype.coe_inj.mp,
    show 2 * (2⁻¹ : ℝ) = 1,
    norm_num,
  },
  dipath_to_path := dipath.stretch_up_is_dipath (_) (by { convert le_refl (2⁻¹ : ℝ), simp [hT], refl, }),
}

def second_part_stretch :
  dipath (0 : I) ⟨2 * (t₁.1 : ℝ) - 1, double_sub_one_mem_I ht₁⟩ :=
{
  to_fun := λ t, dipath.stretch_down (second_part_dipath γ hT₁) (by { convert le_refl (2⁻¹ : ℝ), simp [hT], refl, }) t,
  source' := by {
    simp [hT],
    apply subtype.coe_inj.mp,
    show 2 * (2⁻¹ : ℝ) - 1 = 0,
    norm_num,
  },
  target' := by simp,
  dipath_to_path := dipath.stretch_down_is_dipath (_) (by { convert le_refl (2⁻¹ : ℝ), simp [hT], refl, }),
}

end trans_aux₁

section trans_aux₂

variables {f₂ : D(X, Y)} (F : dihomotopy f₀ f₁) (G: dihomotopy f₁ f₂) (t : I) (x : X)

lemma trans_apply_half_left (ht: t = half_I) : (dihom_to_hom F).trans (dihom_to_hom G) (t, x) = F (1, x) :=
begin
  rw continuous_map.homotopy.trans_apply,
  have ht_coe : (t : ℝ) = 2⁻¹ := subtype.coe_inj.mpr ht,
  have : (t : ℝ) ≤ 2⁻¹ := by linarith,
  simp [this],
  simp [ht_coe],
end

lemma trans_apply_half_right (ht: t = half_I) : (dihom_to_hom F).trans (dihom_to_hom G) (t, x) = G (0, x) :=
begin
  rw continuous_map.homotopy.trans_apply,
  have ht_coe : (t : ℝ) = 2⁻¹ := subtype.coe_inj.mpr ht,
  split_ifs; simp [ht_coe]
end

lemma trans_apply_left (t : I) (x : X) (ht : (t : ℝ) ≤ 2⁻¹) :
  (dihom_to_hom F).trans (dihom_to_hom G) (t, x) = F (⟨2 * t, double_mem_I ht⟩, x) :=
begin
  rw continuous_map.homotopy.trans_apply,
  simp [ht],
  refl,
end

lemma trans_apply_right (t : I) (x : X) (ht : 2⁻¹ ≤ (t : ℝ)) :
  (dihom_to_hom F).trans (dihom_to_hom G) (t, x) = G (⟨2 * t - 1, double_sub_one_mem_I ht⟩, x) :=
begin
  rw continuous_map.homotopy.trans_apply,
  simp [ht],
  split_ifs,
  {
    have : (t : ℝ) = 2⁻¹ := by linarith,
    simp [this],
  },
  refl,
end

end trans_aux₂

section trans_aux₃

variables {f₂ : D(X, Y)} (F : dihomotopy f₀ f₁) (G: dihomotopy f₁ f₂)

lemma trans_first_case {a₀ a₁ : I × X} {γ : path a₀ a₁} (γ_dipath : is_dipath γ) (ht₁ : (a₁.1 : ℝ) ≤ 2⁻¹) :
  is_dipath (γ.map ((dihom_to_hom F).trans (dihom_to_hom G)).continuous_to_fun) :=
begin
  obtain ⟨t₀, x₀⟩ := a₀,
  obtain ⟨t₁, x₁⟩ := a₁,

  set Γ := (dihom_to_hom F).trans (dihom_to_hom G) with Γ_def,

  set γ₁ : dipath t₀ t₁ :=
    {
      to_path := γ.map continuous_fst,
      dipath_to_path := γ_dipath.1
    } with γ₁_def,

  set γ₂ : dipath x₀ x₁ :=
    {
      to_path := γ.map continuous_snd,
      dipath_to_path := γ_dipath.2
    } with γ₂_def,


  set p := dipath.dipath_product (dipath.stretch_up γ₁ ht₁) γ₂ with p_def,
  set p' := p.map (↑F : D(I × X, Y)) with p'_def,

  have h : ∀ (t : I) (x : X), ((t : ℝ) ≤ 2⁻¹) →
    Γ (t, x) = F (⟨2 * (t : ℝ), double_mem_I ᾰ⟩, x),
  {
    intros t x ht,
    rw Γ_def,
    rw continuous_map.homotopy.trans_apply (dihom_to_hom F) (dihom_to_hom G) (t, x),
    simp [ht],
    refl,
  },

  have : (t₀ : ℝ) ≤ 2⁻¹ := le_trans (subtype.coe_le_coe.mp (directed_path_source_le_target γ_dipath.1)) ht₁,
  convert (p'.cast (h t₀ x₀ this) (h t₁ x₁ ht₁)).dipath_to_path,
  ext,
  simp,
  exact h _ _ (le_trans (directed_path_bounded γ_dipath.1).2 ht₁),
end

lemma trans_second_case {a₀ a₁ : I × X} {γ : path a₀ a₁} (γ_dipath : is_dipath γ) (ht₀ : 2⁻¹ ≤ (a₀.1 : ℝ)) :
  is_dipath (γ.map ((dihom_to_hom F).trans (dihom_to_hom G)).continuous_to_fun) :=
begin
  obtain ⟨t₀, x₀⟩ := a₀,
  obtain ⟨t₁, x₁⟩ := a₁,

  set Γ := (dihom_to_hom F).trans (dihom_to_hom G) with Γ_def,

  set γ₁ : dipath t₀ t₁ :=
    {
      to_path := γ.map continuous_fst,
      dipath_to_path := γ_dipath.1
    } with γ₁_def,

  set γ₂ : dipath x₀ x₁ :=
    {
      to_path := γ.map continuous_snd,
      dipath_to_path := γ_dipath.2
    } with γ₂_def,

  set p := dipath.dipath_product (dipath.stretch_down γ₁ ht₀) γ₂ with p_def,
  set p' := p.map (↑G : D(I × X, Y)) with p'_def,

  have h : ∀ (t : I) (x : X), ((2⁻¹ : ℝ) ≤ ↑t) →
    Γ (t, x) = G (⟨2 * (t : ℝ) - 1, double_sub_one_mem_I ᾰ⟩, x),
  {
    intros t x ht,
    rw Γ_def,
    rw continuous_map.homotopy.trans_apply (dihom_to_hom F) (dihom_to_hom G) (t, x),
    split_ifs with ht',
    {
      simp at ht',
      have : ↑t = (2⁻¹ : ℝ) := by linarith,
      simp [this],
    },
    refl,
  },

  have : 2⁻¹ ≤ (t₁ : ℝ) := le_trans ht₀ (subtype.coe_le_coe.mp (directed_path_source_le_target γ₁.dipath_to_path)),
  convert (p'.cast (h t₀ x₀ ht₀) (h t₁ x₁ this)).dipath_to_path,
  ext,
  simp,
  exact h (γ x).1 (γ x).2 (le_trans ht₀ (directed_path_bounded γ_dipath.1).1),
end

end trans_aux₃

end trans_aux

/-
Given `dihomotopy f₀ f₁` and `dihomotopy f₁ f₂`, we can define a `dihomotopy f₀ f₂` by putting the first
dihomotopy on `[0, 1/2]` and the second on `[1/2, 1]`.
-/
def trans {f₀ f₁ f₂ : D(X, Y)} (F : dihomotopy f₀ f₁) (G: dihomotopy f₁ f₂) : dihomotopy f₀ f₂ :=
begin
  set Fₕ := dihom_to_hom F with Fₕ_def,
  set Gₕ := dihom_to_hom G with Gₕ_def,
  set Γ := Fₕ.trans Gₕ with Γ_def,
  have HΓ : directed (↑Γ : C(I × X, Y)) := begin
    rintros ⟨t₀, x₀⟩ ⟨t₁, x₁⟩  γ γ_dipath,

    set γ_as_dipath : dipath (t₀, x₀) (t₁, x₁) :=
      {
        to_path := γ,
        dipath_to_path := γ_dipath
      } with γ_as_dipath_def,

    set γ₁ : dipath t₀ t₁ :=
      {
        to_path := γ.map continuous_fst,
        dipath_to_path := γ_dipath.1
      } with γ₁_def,

    set γ₂ : dipath x₀ x₁ :=
      {
        to_path := γ.map continuous_snd,
        dipath_to_path := γ_dipath.2
      } with γ₂_def,

    by_cases ht₁ : (↑t₁ : ℝ) ≤ 2⁻¹,
    { -- The entire path falls in the domain of F
      exact trans_first_case F G γ_dipath ht₁
    },

    by_cases ht₀ : (↑t₀ : ℝ) < 2⁻¹,
    tactic.swap,
    { -- The entire path falls in the domain of G
      have ht₀ : (2⁻¹ : ℝ) ≤ ↑t₀ := by linarith,
      exact trans_second_case F G γ_dipath ht₀
    },

    {
    -- Complicated
    push_neg at ht₁,
    cases has_T_half (γ.map continuous_fst) ht₀ ht₁ with T hT,
    obtain ⟨hT₀, ⟨hT₁, hT_half⟩⟩ := hT,

    /- Split γ into two parts (one with image in [0, 2⁻¹] × X, the other with image in [2⁻¹, 1] × X)-/
    set a₁ := split_dipath.first_part_dipath γ_as_dipath hT₀ with a₁_def,
    set a₂ := split_dipath.second_part_dipath γ_as_dipath hT₁ with a₂_def,

    /- Create two new paths, where the first coordinate is stretched and the second coordinate remains the same -/
    set p₁ := first_part_stretch γ₁ hT₀ hT₁ (le_of_lt ht₀) hT_half with p₁_def,
    set p₂ := second_part_stretch γ₁ hT₀ hT₁ (le_of_lt ht₁) hT_half with p₂_def,

    set p₁' := split_dipath.first_part_dipath γ₂ hT₀ with p₁'_def,
    set p₂' := split_dipath.second_part_dipath γ₂ hT₁ with p₂'_def,

    set q₁ := (dipath.dipath_product p₁ p₁').map F.to_directed_map with q₁_def,
    set q₂ := (dipath.dipath_product p₂ p₂').map G.to_directed_map with q₂_def,

    set φ := split_dipath.trans_reparam_map hT₀ hT₁ with φ_def,
    have φ₀ : φ 0 = 0 := subtype.ext (split_path.trans_reparam_zero T),
    have φ₁ : φ 1 = 1 := subtype.ext (split_path.trans_reparam_one hT₁),

    have hγT_le_half : ((γ T).1 : ℝ) ≤ 2⁻¹ := subtype.coe_le_coe.mpr (le_of_eq hT_half),
    have hγT_eq_half : ((γ T).1 : ℝ) = 2⁻¹ := subtype.coe_inj.mpr (hT_half),

    set r₁ := q₁.cast (trans_apply_left F G t₀ x₀ (le_of_lt ht₀)) (trans_apply_half_left F G (γ T).1 (γ T).2 hT_half),
    set r₂ := q₂.cast (trans_apply_half_right F G (γ T).1 (γ T).2 hT_half) (trans_apply_right F G t₁ x₁ (le_of_lt ht₁)),

    convert ((r₁.trans r₂).reparam φ φ₀ φ₁).dipath_to_path,
    ext t,

    have hr₁a₁ : r₁.to_path = a₁.to_path.map Γ.continuous_to_fun,
    {
      ext x,
      have : ((a₁ x).1 : ℝ) ≤ 2⁻¹ := le_trans (directed_path_bounded a₁.dipath_to_path.1).2 hγT_le_half,
      calc r₁ x = F (⟨2 * ((a₁ x).1 : ℝ), double_mem_I this⟩, (a₁ x).2) : rfl
        ... = if h : ((a₁ x).1 : ℝ) ≤ 1/2
                then F (⟨2 * ((a₁ x).1 : ℝ), by { simp at h, exact double_mem_I h }⟩, (a₁ x).2)
                else G (⟨2 * ((a₁ x).1 : ℝ) - 1, by { simp at h, exact double_sub_one_mem_I (le_of_lt h) }⟩, (a₁ x).2)
              : by simp [this]
        ... = if h : ((a₁ x).1 : ℝ) ≤ 1/2
                then Fₕ (⟨2 * ((a₁ x).1 : ℝ), by { simp at h, exact double_mem_I h }⟩, (a₁ x).2)
                else Gₕ (⟨2 * ((a₁ x).1 : ℝ) - 1, by { simp at h, exact double_sub_one_mem_I (le_of_lt h) }⟩, (a₁ x).2) : rfl
        ... = (Fₕ.trans Gₕ) (a₁ x) : (continuous_map.homotopy.trans_apply Fₕ Gₕ (a₁ x)).symm
        ... = Γ (a₁ x) : by rw Γ_def
        ... = (a₁.to_path.map Γ.continuous_to_fun) x : rfl
    },
    have hr₂a₂ : r₂.to_path = a₂.to_path.map Γ.continuous_to_fun,
    {
      ext,
      have : 2⁻¹ ≤ ((a₂ x).1 : ℝ),
      {
        have : (2⁻¹ : ℝ) = ↑(γ T).1 := subtype.coe_inj.mpr hT_half.symm,
        calc (2⁻¹ : ℝ) = ↑(γ T).1 : this
            ... ≤  ↑(a₂ x).1 : (directed_path_bounded a₂.dipath_to_path.1).1
      },
      calc r₂.to_path x = G (⟨2 * ((a₂ x).1 : ℝ) - 1, double_sub_one_mem_I this⟩, (a₂ x).2) : rfl
            ... = if h : ((a₂ x).1 : ℝ) ≤ 1/2
                    then F (⟨2 * ((a₂ x).1 : ℝ), by { simp at h, exact double_mem_I h }⟩, (a₂ x).2)
                    else G (⟨2 * ((a₂ x).1 : ℝ) - 1,  by { simp at h, exact double_sub_one_mem_I (le_of_lt h) }⟩, (a₂ x).2) :
                      by {
                            split_ifs with h,
                            {
                              simp at h,
                              have hγ₂x : ((a₂ x).1 : ℝ) = 2⁻¹ := by linarith,
                              simp [hγ₂x],
                            },
                            refl,
                         }
            ... = if h : ((a₂ x).1 : ℝ) ≤ 1/2
                    then Fₕ (⟨2 * ((a₂ x).1 : ℝ), by { simp at h, exact double_mem_I h }⟩, (a₂ x).2)
                    else Gₕ (⟨2 * ((a₂ x).1 : ℝ) - 1, by { simp at h, exact double_sub_one_mem_I (le_of_lt h) }⟩, (a₂ x).2) : rfl
            ... = (Fₕ.trans Gₕ) (a₂ x) : (continuous_map.homotopy.trans_apply Fₕ Gₕ (a₂ x)).symm
            ... = Γ (a₂ x) : by rw Γ_def
            ... = (a₂.to_path.map Γ.continuous_to_fun) x : rfl
    },
    calc (Γ ∘ γ) t = Γ (γ t) : rfl
          ...    = Γ (((a₁.trans a₂).reparam φ φ₀ φ₁) t) : by { rw ←split_dipath.first_trans_second_reparam_eq_self γ_as_dipath hT₀ hT₁, refl }
          ...    = ((a₁.trans a₂).to_path.map Γ.continuous_to_fun).reparam φ φ.continuous_to_fun φ₀ φ₁ t : by refl
          ...    = ((a₁.to_path.trans a₂.to_path).map Γ.continuous_to_fun).reparam φ φ.continuous_to_fun φ₀ φ₁ t : by refl
          ...    = ((a₁.to_path.map Γ.continuous_to_fun).trans (a₂.to_path.map Γ.continuous_to_fun)).reparam φ φ.continuous_to_fun φ₀ φ₁ t :
                                                                            by rw path.map_trans a₁.to_path a₂.to_path (Γ.continuous_to_fun)
          ...    = (r₁.to_path.trans r₂.to_path).reparam φ φ.continuous_to_fun φ₀ φ₁ t : by rw [hr₁a₁, hr₂a₂]
          ...    = (r₁.trans r₂).reparam φ φ₀ φ₁ t : by refl
    }
  end,
  exact hom_to_dihom Γ HΓ,
end

lemma trans_apply {f₀ f₁ f₂ : D(X, Y)} (F : dihomotopy f₀ f₁) (G : dihomotopy f₁ f₂) (x : I × X) :
  (F.trans G) x =
  if h : (x.1 : ℝ) ≤ 1/2 then
    F (⟨2 * x.1, (unit_interval.mul_pos_mem_iff zero_lt_two).2 ⟨x.1.2.1, h⟩⟩, x.2)
  else
    G (⟨2 * x.1 - 1, unit_interval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, x.1.2.2⟩⟩, x.2) :=
begin
  set Fₕ := dihom_to_hom F with Fₕ_def,
  set Gₕ := dihom_to_hom G with Gₕ_def,
  set Γ := Fₕ.trans Gₕ with Γ_def,
  have : (Fₕ.trans Gₕ) x = (F.trans G) x := rfl,
  rw ←this,
  exact continuous_map.homotopy.trans_apply Fₕ Gₕ x,
end

/--
Casting a `dihomotopy f₀ f₁` to a `dihomotopy g₀ g₁` where `f₀ = g₀` and `f₁ = g₁`.
-/
@[simps]
def cast {f₀ f₁ g₀ g₁ : D(X, Y)} (F : dihomotopy f₀ f₁) (h₀ : f₀ = g₀) (h₁ : f₁ = g₁) :
  dihomotopy g₀ g₁ :=
{
  to_fun := F,
  directed_to_fun := F.directed_to_fun,
  map_zero_left' := by simp [←h₀],
  map_one_left' := by simp [←h₁]
}

lemma cast_apply {f₀ f₁ g₀ g₁ : D(X, Y)} (F : dihomotopy f₀ f₁) (h₀ : f₀ = g₀) (h₁ : f₁ = g₁) (t : I × X) :
  F.cast h₀ h₁ t = F t := rfl

/--
If we have a `dihomotopy f₀ f₁` and a `dihomotopy g₀ g₁`, then we can compose them and get a
`dihomotopy (g₀.comp f₀) (g₁.comp f₁)`.
-/
@[simps]
def hcomp {f₀ f₁ : D(X, Y)} {g₀ g₁ : D(Y, Z)} (F : dihomotopy f₀ f₁) (G : dihomotopy g₀ g₁)
  : dihomotopy (g₀.comp f₀) (g₁.comp f₁) :=
begin
  set Fₕ := dihom_to_hom F with Fₕ_def,
  set Gₕ := dihom_to_hom G with Gₕ_def,
  set Γ := Fₕ.hcomp Gₕ with Γ_def,
  exact hom_to_dihom Γ (G.comp (directed_fst.prod_map_mk ↑F)).directed_to_fun,
end

end dihomotopy

/--
  Given directed maps `f₀` and `f₁`, we say `f₀` and `f₁` are pre_dihomotopic if there exists a
  `dihomotopy f₀ f₁`.
-/
def pre_dihomotopic (f₀ f₁ : D(X, Y)) : Prop := nonempty (dihomotopy f₀ f₁)

/--
  Given directed maps `f₀` and `f₁`, we say `f₀` and `f₁` are dihomotopic if there
  is a chain of pre_dihomotopic maps leading from `f₀` to `f₁`.
  In other words, dihomotopic is the equivalence relation generated by pre_dihomotopic.
-/
def dihomotopic (f₀ f₁ : D(X, Y)) : Prop := (eqv_gen pre_dihomotopic) f₀ f₁

namespace dihomotopic

lemma equivalence : equivalence (@dihomotopic X Y _ _) := by apply eqv_gen.is_equivalence

end dihomotopic

/--
The type of dihomotopies between `f₀ f₁ : D(X, Y)`, where the intermediate maps satisfy the predicate
`P : D(X, Y) → Prop`
-/
structure dihomotopy_with (f₀ f₁ : D(X, Y)) (P : D(X, Y) → Prop) extends dihomotopy f₀ f₁ :=
(
  prop' : ∀ (t : I), P (to_directed_map.prod_const_fst t)
)

namespace dihomotopy_with

section

variables {f₀ f₁ : D(X, Y)} {P : D(X, Y) → Prop}

instance : has_coe_to_fun (dihomotopy_with f₀ f₁ P) (λ _, I × X → Y) := ⟨λ F, F.to_fun⟩

lemma coe_fn_injective : @function.injective (dihomotopy_with f₀ f₁ P) (I × X → Y) coe_fn :=
begin
  rintros ⟨⟨⟨⟨F, _⟩, _⟩, _⟩, _⟩ ⟨⟨⟨⟨G, _⟩, _⟩, _⟩, _⟩ h,
  congr' 4,
end

@[ext]
lemma ext {F G : dihomotopy_with f₀ f₁ P} (h : ∀ x, F x = G x) : F = G :=
coe_fn_injective $ funext h

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
because it is a composition of multiple projections. -/
def simps.apply (F : dihomotopy_with f₀ f₁ P) : I × X → Y := F

initialize_simps_projections dihomotopy_with
  (to_dihomotopy_to_directed_map_to_continuous_map_to_fun -> apply, -to_dihomotopy_to_directed_map_to_continuous_map)

@[continuity]
protected lemma continuous (F : dihomotopy_with f₀ f₁ P) : continuous F := F.continuous_to_fun

@[simp]
lemma apply_zero (F : dihomotopy_with f₀ f₁ P) (x : X) : F (0, x) = f₀ x := F.map_zero_left' x

@[simp]
lemma apply_one (F : dihomotopy_with f₀ f₁ P) (x : X) : F (1, x) = f₁ x := F.map_one_left' x

@[simp]
lemma coe_to_continuous_map (F : dihomotopy_with f₀ f₁ P) : ⇑F.to_continuous_map = F := rfl

@[simp]
lemma coe_to_dihomotopy (F : dihomotopy_with f₀ f₁ P) : ⇑F.to_dihomotopy = F := rfl

lemma prop (F : dihomotopy_with f₀ f₁ P) (t : I) : P (F.to_dihomotopy.curry t) := F.prop' t

end

variable {P : D(X, Y) → Prop}

/--
Given a directed map `f`, and a proof `h : P f`, we can define a `dihomotopy_with f f P` by `F (t, x) = f x`
-/
@[simps]
def refl (f : D(X, Y)) (hf : P f) : dihomotopy_with f f P :=
{
  prop' := begin
    intro t,
    convert hf,
    ext,
    refl,
  end,
  ..dihomotopy.refl f
}

instance : inhabited (dihomotopy_with (directed_map.id X) (directed_map.id X) (λ f, true)) := ⟨dihomotopy_with.refl _ trivial⟩

/--
Given `dihomotopy_with f₀ f₁ P` and `dihomotopy_with f₁ f₂ P`, we can define a `dihomotopy_with f₀ f₂ P`
by putting the first dihomotopy on `[0, 1/2]` and the second on `[1/2, 1]`.
-/
def trans {f₀ f₁ f₂ : D(X, Y)} (F : dihomotopy_with f₀ f₁ P) (G : dihomotopy_with f₁ f₂ P) :
  dihomotopy_with f₀ f₂ P :=
{
  prop' := λ t,
  begin
    simp only [dihomotopy.trans],
    change P ⟨⟨λ _, ite ((t : ℝ) ≤ _) _ _, _⟩, _⟩,
    split_ifs,
    {
      have : ((t : ℝ) ≤ 2⁻¹) := by { simp at h, exact h },
      convert F.prop' ⟨2 * (t : ℝ), double_mem_I this⟩,
      ext,
      change ((F.to_dihomotopy.dihom_to_hom.extend) (2 * t : ℝ)) x = F.to_dihomotopy.dihom_to_hom (⟨2 * (t : ℝ), _⟩, x),
      rw ←continuous_map.homotopy.extend_apply_coe F.to_dihomotopy.dihom_to_hom _ x,
      refl,
    },
    {
      have : (2⁻¹ ≤ (t : ℝ)) := by { simp at h, linarith },
      convert G.prop' ⟨2 * (t : ℝ) - 1, double_sub_one_mem_I this⟩,
      ext,
      change ((G.to_dihomotopy.dihom_to_hom.extend) (2 * (t : ℝ) - 1)) x = G.to_dihomotopy.dihom_to_hom (⟨2 * (t : ℝ) - 1, _⟩, x),
      rw ←continuous_map.homotopy.extend_apply_coe G.to_dihomotopy.dihom_to_hom _ x,
      refl,
    },
  end
  ..F.to_dihomotopy.trans G.to_dihomotopy
}

lemma trans_apply {f₀ f₁ f₂ : D(X, Y)} (F : dihomotopy_with f₀ f₁ P) (G : dihomotopy_with f₁ f₂ P)
  (x : I × X) : (F.trans G) x =
  if h : (x.1 : ℝ) ≤ 1/2 then
    F (⟨2 * x.1, (unit_interval.mul_pos_mem_iff zero_lt_two).2 ⟨x.1.2.1, h⟩⟩, x.2)
  else
    G (⟨2 * x.1 - 1, unit_interval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, x.1.2.2⟩⟩, x.2) :=
dihomotopy.trans_apply _ _ _

/--
Casting a `dihomotopy_with f₀ f₁ P` to a `dihomotopy_with g₀ g₁ P` where `f₀ = g₀` and `f₁ = g₁`.
-/
@[simps]
def cast {f₀ f₁ g₀ g₁ : D(X, Y)} (F : dihomotopy_with f₀ f₁ P) (h₀ : f₀ = g₀) (h₁ : f₁ = g₁) :
  dihomotopy_with g₀ g₁ P :=
{
  prop' := F.prop,
  ..F.to_dihomotopy.cast h₀ h₁
}

end dihomotopy_with

/--
Given directed maps `f₀` and `f₁`, we say `f₀` and `f₁` are pre_dihomotopic with respect to the
predicate `P` if there exists a `dihomotopy_with f₀ f₁ P`.
-/
def pre_dihomotopic_with (P : D(X, Y) → Prop) (f₀ f₁ : D(X, Y)): Prop :=
nonempty (dihomotopy_with f₀ f₁ P)

/--
`dihomotopic_with` is the equivalence relation generated by `pre_dihomotopic_with`.
-/
def dihomotopic_with (P : D(X, Y) → Prop) (f₀ f₁ : D(X, Y)) : Prop := eqv_gen (pre_dihomotopic_with P) f₀ f₁


/--
A `dihomotopy_rel f₀ f₁ S` is a dihomotopy between `f₀` and `f₁` which is fixed on the points in `S`.
-/
abbreviation dihomotopy_rel (f₀ f₁ : D(X, Y)) (S : set X) :=
  dihomotopy_with f₀ f₁ (λ f, ∀ x ∈ S, f x = f₀ x ∧ f x = f₁ x)

namespace dihomotopy_rel

section

variables {f₀ f₁ : D(X, Y)} {S : set X}

lemma eq_fst (F : dihomotopy_rel f₀ f₁ S) (t : I) {x : X} (hx : x ∈ S) :
  F (t, x) = f₀ x := (F.prop t x hx).1

lemma eq_snd (F : dihomotopy_rel f₀ f₁ S) (t : I) {x : X} (hx : x ∈ S) :
  F (t, x) = f₁ x := (F.prop t x hx).2

lemma fst_eq_snd (F : dihomotopy_rel f₀ f₁ S) {x : X} (hx : x ∈ S) :
  f₀ x = f₁ x := F.eq_fst 0 hx ▸ F.eq_snd 0 hx

end

variables {f₀ f₁ f₂ : D(X, Y)} {S : set X}

/--
Given a map `f : D(X, Y)` and a set `S`, we can define a `dihomotopy_rel f f S` by setting
`F (t, x) = f x` for all `t`. This is defined using `dihomotopy_with.refl`, but with the proof
filled in.
-/
@[simps]
def refl (f : D(X, Y)) (S : set X) : dihomotopy_rel f f S :=
dihomotopy_with.refl f (λ x hx, ⟨rfl, rfl⟩)

/--
Given `dihomotopy_rel f₀ f₁ S` and `dihomotopy_rel f₁ f₂ S`, we can define a `dihomotopy_rel f₀ f₂ S`
by putting the first dihomotopy on `[0, 1/2]` and the second on `[1/2, 1]`.
-/
def trans (F : dihomotopy_rel f₀ f₁ S) (G : dihomotopy_rel f₁ f₂ S) : dihomotopy_rel f₀ f₂ S :=
{
  prop' := λ t,
  begin
    intros x hx,
    simp only [dihomotopy.trans],
    change
      (⟨⟨λ _, ite ((t : ℝ) ≤ _) _ _, _⟩, _⟩ : D(X, Y)) _ = _ ∧
      (⟨⟨λ _, ite ((t : ℝ) ≤ _) _ _, _⟩, _⟩ : D(X, Y)) _ = _,
    split_ifs,
    {
      have : ((t : ℝ) ≤ 2⁻¹) := by { simp at h, exact h },
      set t' : I := ⟨2 * (t : ℝ), double_mem_I this⟩ with t'_def,

      have h₁ : F (t', x) = f₀ x := F.eq_fst t' hx,
      have h₂ : F (t', x) = f₂ x := (F.eq_snd t' hx).trans (G.fst_eq_snd hx),
      have : (F (t', x) = f₀ x) ∧ (F (t', x) = f₂ x) := ⟨h₁, h₂⟩,
      convert this; {
        change ((F.to_dihomotopy.dihom_to_hom.extend) (2 * t : ℝ)) x = F.to_dihomotopy.dihom_to_hom (⟨2 * (t : ℝ), _⟩, x),
        rw ←continuous_map.homotopy.extend_apply_coe F.to_dihomotopy.dihom_to_hom _ x,
        refl,
      }
    },
    {
      have : (2⁻¹ ≤ (t : ℝ)) := by { simp at h, linarith },
      set t' : I := ⟨2 * (t : ℝ) - 1, double_sub_one_mem_I this⟩ with t'_def,

      have h₁ : G (t', x) = f₀ x := (G.eq_fst t' hx).trans (F.fst_eq_snd hx).symm,
      have h₂ : G (t', x) = f₂ x := G.eq_snd t' hx,

      convert and.intro h₁ h₂ ; {
        change ((G.to_dihomotopy.dihom_to_hom.extend) (2 * (t : ℝ) - 1)) x = G.to_dihomotopy.dihom_to_hom (⟨2 * (t : ℝ) - 1, _⟩, x),
        rw ←continuous_map.homotopy.extend_apply_coe G.to_dihomotopy.dihom_to_hom _ x,
        refl,
      }
    },
  end,
  ..dihomotopy.trans F.to_dihomotopy G.to_dihomotopy
}

lemma trans_apply (F : dihomotopy_rel f₀ f₁ S) (G : dihomotopy_rel f₁ f₂ S)
  (x : I × X) : (F.trans G) x =
  if h : (x.1 : ℝ) ≤ 1/2 then
    F (⟨2 * x.1, (unit_interval.mul_pos_mem_iff zero_lt_two).2 ⟨x.1.2.1, h⟩⟩, x.2)
  else
    G (⟨2 * x.1 - 1, unit_interval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, x.1.2.2⟩⟩, x.2) :=
dihomotopy.trans_apply _ _ _

/--
Casting a `dihomotopy_rel f₀ f₁ S` to a `dihomotopy_rel g₀ g₁ S` where `f₀ = g₀` and `f₁ = g₁`.
-/
@[simps]
def cast {f₀ f₁ g₀ g₁ : D(X, Y)} (F : dihomotopy_rel f₀ f₁ S) (h₀ : f₀ = g₀) (h₁ : f₁ = g₁) : dihomotopy_rel g₀ g₁ S :=
{ prop' := λ t x hx, by { simpa [←h₀, ←h₁] using F.prop t x hx },
  ..dihomotopy.cast F.to_dihomotopy h₀ h₁ }

end dihomotopy_rel

/--
Given directed maps `f₀` and `f₁`, we say `f₀` and `f₁` are pre_dihomotopic relative to a set `S` if
there exists a `dihomotopy_rel f₀ f₁ S`.
-/
def pre_dihomotopic_rel (S : set X) (f₀ f₁ : D(X, Y)) : Prop :=
nonempty (dihomotopy_rel f₀ f₁ S)

/--
`dihomotopic_rel` is the equivalence relation generated by `pre_dihomotopic_rel`.
-/
def dihomotopic_rel (S : set X) (f₀ f₁ : D(X, Y)) : Prop := eqv_gen (pre_dihomotopic_rel S) f₀ f₁

namespace dihomotopic_rel

variable {S : set X}

lemma equivalence : equivalence (λ f g : D(X, Y), dihomotopic_rel S f g) := by apply eqv_gen.is_equivalence

end dihomotopic_rel

end directed_map

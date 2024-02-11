import Lean4.directed_homotopy
import Lean4.trans_refl
import Mathlib.Topology.Homotopy.Path

/-
  This file contains the definition of a directed path homotopy, or `Dipath.Dihomotopy`:
  It is a dihomotopy between two paths that keeps the endpoints fixed.

  We prove a few constructions and define the equivalence relation `Dihomtopic` between two paths.
  We show that this relation is closed under reparametrizations, and that concatenation and directed maps respect it.

  Much of the structure of this file is based on the undirected version:
  https://github.com/leanprover-community/mathlib/blob/master/src/topology/homotopy/path.lean
-/

universe u v

open unitIAux
open DirectedUnitInterval
open scoped unitInterval

variable {X : Type u} {Y : Type v}
variable [DirectedSpace X] [DirectedSpace Y]
variable {x₀ x₁ x₂ x₃ : X}

noncomputable section

namespace Dipath

/--
The type of dihomotopies between two directed paths.
-/
abbrev Dihomotopy (p₀ p₁ : Dipath x₀ x₁) :=
  DirectedMap.DihomotopyRel p₀.toDirectedMap p₁.toDirectedMap {0, 1}

namespace Dihomotopy

section

variable {p₀ p₁ : Dipath x₀ x₁}

-- TODO: Unnecessary?
instance : CoeFun (Dihomotopy p₀ p₁) (fun _ => I × I → X) := ⟨fun F => F.toFun⟩

lemma coeFn_injective : @Function.Injective (Dihomotopy p₀ p₁) (I × I → X) (⇑) :=
  DFunLike.coe_injective

@[simp]
lemma source (F : Dihomotopy p₀ p₁) (t : I) : F (t, 0) = x₀ := by
  calc F (t, 0)
    _ = p₀ 0 := DirectedMap.DihomotopyRel.eq_fst _ _ (.inl rfl)
    _ = x₀ := p₀.source

@[simp]
lemma target (F : Dihomotopy p₀ p₁) (t : I) : F (t, 1) = x₁ := by
  calc F (t, 1)
    _ = p₀ 1 := DirectedMap.DihomotopyRel.eq_fst _ _ (.inr rfl)
    _ = x₁ := p₀.target

/-- A `F : Dihomotopy ↑p₁ ↑p₂` between two dipaths `p₁ p₂ : Dipath x₁ x₂` can be coerced into a dihomotopy,
  if it is directed -/
def hom_to_dihom (F : Path.Homotopy p₀.toPath p₁.toPath)
  (HF : DirectedMap.Directed F.toContinuousMap) : Dihomotopy p₀ p₁ where
  toFun := F.toFun
  continuous_toFun := F.continuous_toFun
  directed_toFun := HF
  map_zero_left := F.map_zero_left
  map_one_left := F.map_one_left
  prop' := sorry -- F.prop'

/-- A Dihomotopy `F` between two Dipaths `p₁ p₂` can be coerced into a Homotopy between `p₀.toPath`
 and `p₁.toPath`-/
def dihom_to_hom (F : Dihomotopy p₀ p₁) : Path.Homotopy p₀.toPath p₁.toPath where
  toFun := F.toFun
  continuous_toFun := F.continuous_toFun
  map_zero_left := F.map_zero_left
  map_one_left := F.map_one_left
  prop' := sorry -- F.prop'

instance coe_dihom_to_hom : Coe (Dihomotopy p₀ p₁) (Path.Homotopy p₀.toPath p₁.toPath) :=
  ⟨fun F => F.dihom_to_hom⟩

/--
Evaluating a dipath homotopy at an intermediate point, giving us a `dipath`.
-/
def eval (F : Dihomotopy p₀ p₁) (t : I) : Dipath x₀ x₁ where
  toFun := F.toDihomotopy.curry t
  source' := by simp; exact F.source _ -- TODO: Why does simp not understand source?
  target' := by simp; exact F.target _
  dipath_toPath := DirectedUnitInterval.isDipath_of_isDipath_comp_id
    $ (F.toDihomotopy.curry t).directed_toFun DirectedUnitInterval.IdentityPath
      DirectedUnitInterval.isDipath_identityPath

@[simp]
lemma coe_eval (F : Dihomotopy p₀ p₁) (t : I) :
  (⇑(F.eval t) : I → X)  = ⇑(F.toDihomotopy.curry t) := rfl

@[simp]
lemma eval_zero (F : Dihomotopy p₀ p₁) : F.eval 0 = p₀ := by
  ext t
  simp [eval]

@[simp]
lemma eval_one (F : Dihomotopy p₀ p₁) : F.eval 1 = p₁ := by
  ext t
  simp [eval]

end

section
variable {p₀ p₁ p₂ : Dipath x₀ x₁}

/--
Given a dipath `p`, we can define a `Dihomotopy p p` by `F (t, x) = p x`
-/
@[simps!]
def refl (p : Dipath x₀ x₁) : Dihomotopy p p :=
  DirectedMap.DihomotopyRel.refl p.toDirectedMap {0, 1}

/--
Given `Dihomotopy p₀ p₁` and `Dihomotopy p₁ p₂`, we can define a `Dihomotopy p₀ p₂` by putting the first
dihomotopy on `[0, 1/2]` and the second on `[1/2, 1]`.
-/
def trans (F : Dihomotopy p₀ p₁) (G : Dihomotopy p₁ p₂) : Dihomotopy p₀ p₂ :=
  DirectedMap.DihomotopyRel.trans F G

lemma trans_apply (F : Dihomotopy p₀ p₁) (G : Dihomotopy p₁ p₂) (x : I × I) :
  (F.trans G) x =
    if h : (x.1 : ℝ) ≤ 1/2 then
      F (⟨2 * x.1, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨x.1.2.1, h⟩⟩, x.2)
    else
      G (⟨2 * x.1 - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, x.1.2.2⟩⟩, x.2) :=
DirectedMap.DihomotopyRel.trans_apply _ _ _

/--
Casting a `Dihomotopy p₀ p₁` to a `Dihomotopy q₀ q₁` where `p₀ = q₀` and `p₁ = q₁`.
-/
-- @[simps]
def cast {p₀ p₁ q₀ q₁ : Dipath x₀ x₁} (F : Dihomotopy p₀ p₁) (h₀ : p₀ = q₀) (h₁ : p₁ = q₁) :
    Dihomotopy q₀ q₁ :=
  DirectedMap.DihomotopyRel.cast F (congr_arg _ h₀) (congr_arg _ h₁)

end

section

variable {p₀ q₀ : Dipath x₀ x₁} {p₁ q₁ : Dipath x₁ x₂}

section hcomp_aux

variable (F : Dihomotopy p₀ q₀) (G: Dihomotopy p₁ q₁) (s t : I) (ht: t = half_I)

lemma hcomp_apply_half_left (ht: t = half_I) :
    (dihom_to_hom F).hcomp (dihom_to_hom G) (s, t) = F (s, 1) := by
  rw [Path.Homotopy.hcomp_apply]
  have ht_coe : (t : ℝ) = 2⁻¹ := Subtype.coe_inj.mpr ht
  have : (t : ℝ) ≤ 2⁻¹ := by linarith
  simp [this, ht_coe]

lemma hcomp_apply_half_right (ht: t = half_I) :
    (dihom_to_hom F).hcomp (dihom_to_hom G) (s, t) = G (s, 0) := by
  rw [Path.Homotopy.hcomp_apply]
  have ht_coe : (t : ℝ) = 2⁻¹ := Subtype.coe_inj.mpr ht
  split_ifs <;> simp [ht_coe]

lemma hcomp_apply_left (ht : (t : ℝ) ≤ 2⁻¹) :
    (dihom_to_hom F).hcomp (dihom_to_hom G) (s, t) = F (s, ⟨2 * t, double_mem_I ht⟩) := by
  rw [Path.Homotopy.hcomp_apply]
  simp [ht]
  rfl

lemma hcomp_apply_right (ht : 2⁻¹ ≤ (t : ℝ)) :
    (dihom_to_hom F).hcomp (dihom_to_hom G) (s, t) = G (s, ⟨2 * t - 1, double_sub_one_mem_I ht⟩) := by
  rw [Path.Homotopy.hcomp_apply]
  simp [ht]
  split_ifs
  · have : (t : ℝ) = 2⁻¹ := by linarith
    simp [this]
    exact (G.source _).symm
  · rfl

lemma hcomp_first_case (F : Dihomotopy p₀ q₀) (G : Dihomotopy p₁ q₁) {a₀ a₁ : I × I} {γ : Path a₀ a₁}
  (γ_dipath : IsDipath γ) (ht₁ : (a₁.2 : ℝ) ≤ 2⁻¹) :
    IsDipath (γ.map ((dihom_to_hom F).hcomp (dihom_to_hom G)).continuous_toFun) := by
  obtain ⟨s₀, t₀⟩ := a₀
  obtain ⟨s₁, t₁⟩ := a₁

  set Γ := (dihom_to_hom F).hcomp (dihom_to_hom G)

  set γ₁ : Dipath s₀ s₁ :=
    {
      toPath := γ.map continuous_fst
      dipath_toPath := γ_dipath.1
    }

  set γ₂ : Dipath t₀ t₁ :=
    {
      toPath := γ.map continuous_snd
      dipath_toPath := γ_dipath.2
    }

  set p := Dipath.dipath_product γ₁ (Dipath.stretch_up γ₂ ht₁)
  set p' := p.map (F.toDirectedMap)

  have h : ∀ (s t : I), (h : (t : ℝ) ≤ 2⁻¹) → Γ (s, t) = F (s, ⟨2 * (t : ℝ), double_mem_I h⟩) := by
    intros s t ht
    rw [Path.Homotopy.hcomp_apply (dihom_to_hom F) (dihom_to_hom G) (s, t)]
    simp [ht]
    rfl

  have ht₀ : (t₀ : ℝ) ≤ 2⁻¹ :=
    le_trans (Subtype.coe_le_coe.mp (directed_path_source_le_target γ_dipath.2)) ht₁

  convert (p'.cast (h s₀ t₀ ht₀) (h s₁ t₁ ht₁)).dipath_toPath
  ext
  simp
  exact h _ _ (le_trans (directed_path_bounded γ_dipath.2 _).2 ht₁)


lemma hcomp_second_case (F : Dihomotopy p₀ q₀) (G : Dihomotopy p₁ q₁) {a₀ a₁ : I × I}
  {γ : Path a₀ a₁} (γ_dipath : IsDipath γ) (ht₀ : 2⁻¹ ≤ (a₀.2 : ℝ)) :
    IsDipath (γ.map ((dihom_to_hom F).hcomp (dihom_to_hom G)).continuous_toFun) := by
  obtain ⟨s₀, t₀⟩ := a₀
  obtain ⟨s₁, t₁⟩ := a₁

  set Γ := (dihom_to_hom F).hcomp (dihom_to_hom G)

  set γ₁ : Dipath s₀ s₁ :=
    {
      toPath := γ.map continuous_fst
      dipath_toPath := γ_dipath.1
    }

  set γ₂ : Dipath t₀ t₁ :=
    {
      toPath := γ.map continuous_snd
      dipath_toPath := γ_dipath.2
    }

  set p := Dipath.dipath_product γ₁ (Dipath.stretch_down γ₂ ht₀)
  set p' := p.map G.toDirectedMap

  have h : ∀ (s t : I), (h : (2⁻¹ : ℝ) ≤ ↑t) →
    Γ (s, t) = G (s, ⟨2 * (t : ℝ) - 1, double_sub_one_mem_I h⟩) := by
    intros s t ht
    rw [Path.Homotopy.hcomp_apply (dihom_to_hom F) (dihom_to_hom G) (s, t)]
    split_ifs with ht'
    · simp at ht'
      have : ↑t = (2⁻¹ : ℝ) := by linarith
      simp [this]
    · rfl

  have ht₁ : 2⁻¹ ≤ (t₁ : ℝ) := le_trans ht₀ (Subtype.coe_le_coe.mp (directed_path_source_le_target γ_dipath.2))
  convert (p'.cast (h s₀ t₀ ht₀) (h s₁ t₁ ht₁)).dipath_toPath
  ext x
  simp
  exact h (γ x).1 (γ x).2 (le_trans ht₀ (directed_path_bounded γ_dipath.2 _).1)

end hcomp_aux

/--
Suppose `p₀` and `q₀` are dipaths from `x₀` to `x₁`, `p₁` and `q₁` are dipaths from `x₁` to `x₂`.
Furthermore, suppose `F : Dihomotopy p₀ q₀` and `G : Dihomotopy p₁ q₁`. Then we can define a dihomotopy
from `p₀.trans p₁` to `q₀.trans q₁`.
-/
def hcomp (F : Dihomotopy p₀ q₀) (G : Dihomotopy p₁ q₁) :
    Dihomotopy (p₀.trans p₁) (q₀.trans q₁) := by
  set Fₕ := dihom_to_hom F
  set Gₕ := dihom_to_hom G
  set Γ := Fₕ.hcomp Gₕ
  have : DirectedMap.Directed Γ.toContinuousMap := by
    rintro ⟨s₀, t₀⟩ ⟨s₁, t₁⟩ γ γ_dipath

    set γ_as_dipath : Dipath (s₀, t₀) (s₁, t₁) :=
      {
        toPath := γ,
        dipath_toPath := γ_dipath
      }
    set γ₁ : Dipath s₀ s₁ :=
      {
        toPath := γ.map continuous_fst
        dipath_toPath := γ_dipath.1
      }
    set γ₂ : Dipath t₀ t₁ :=
      {
        toPath := γ.map continuous_snd
        dipath_toPath := γ_dipath.2
      }

    by_cases ht₁ : (↑t₁ : ℝ) ≤ 2⁻¹
    case pos => exact hcomp_first_case F G γ_dipath ht₁

    by_cases ht₀ : (↑t₀ : ℝ) < 2⁻¹
    case neg => exact hcomp_second_case F G γ_dipath (by linarith)

    -- Complicated
    push_neg at ht₁
    cases' has_T_half (γ.map continuous_snd) ht₀ ht₁ with T hT
    obtain ⟨hT₀, ⟨hT₁, hT_half⟩⟩ := hT

    /- Split γ into two parts (one with image in I × [0, 2⁻¹], the other with image in I × [2⁻¹, 1])-/
    set a₁ := SplitDipath.first_part_dipath γ_as_dipath T
    set a₂ := SplitDipath.second_part_dipath γ_as_dipath T

    /- Create two new paths, where the first coordinate is stretched and the second coordinate remains the same -/
    set p₁ := SplitDipath.first_part_dipath γ₁ T
    set p₂ := SplitDipath.second_part_dipath γ₁ T

    set p₁' := DirectedMap.Dihomotopy.FirstPartStretch γ₂ hT_half (le_of_lt ht₀)
    set p₂' := DirectedMap.Dihomotopy.SecondPartStretch γ₂ hT_half (le_of_lt ht₁)

    set q₁ := (Dipath.dipath_product p₁ p₁').map F.toDirectedMap
    set q₂ := (Dipath.dipath_product p₂ p₂').map G.toDirectedMap

    set φ := SplitDipath.trans_reparam_map hT₀ hT₁
    have φ₀ : φ 0 = 0 := Subtype.ext $ SplitPath.trans_reparam_zero T
    have φ₁ : φ 1 = 1 := Subtype.ext $ SplitPath.trans_reparam_one hT₁

    have hγT_eq_half : ((γ T).2 : ℝ) = 2⁻¹ := Subtype.coe_inj.mpr hT_half
    have hγT_le_half : ((γ T).2 : ℝ) ≤ 2⁻¹ := le_of_eq hγT_eq_half

    set r₁ := q₁.cast (hcomp_apply_left F G s₀ t₀ (le_of_lt ht₀)) (hcomp_apply_half_left F G (γ T).1 (γ T).2 hT_half)
    set r₂ := q₂.cast (hcomp_apply_half_right F G (γ T).1 (γ T).2 hT_half) (hcomp_apply_right F G s₁ t₁ (le_of_lt ht₁))

    convert ((r₁.trans r₂).reparam φ φ₀ φ₁).dipath_toPath
    ext t

    have hr₁a₁ : r₁.toPath = a₁.toPath.map Γ.continuous_toFun := sorry
    /- TODO: Update to Lean4
      ext x,
      have : ((a₁ x).2 : ℝ) ≤ 2⁻¹ := le_trans (directed_path_bounded a₁.dipath_to_path.2).2 hγT_le_half,
      calc r₁ x = F ((a₁ x).1, ⟨2 * ((a₁ x).2 : ℝ), double_mem_I this⟩) : rfl
        ... = if h : ((a₁ x).2 : ℝ) ≤ 1/2
                then F ((a₁ x).1, ⟨2 * ((a₁ x).2 : ℝ), by { apply double_mem_I, convert h, norm_num }⟩)
                else G ((a₁ x).1, ⟨2 * ((a₁ x).2 : ℝ) - 1, by { apply double_sub_one_mem_I (le_of_lt _), convert h, norm_num }⟩)
              : by simp [this]
        ... = if h : ((a₁ x).2 : ℝ) ≤ 1/2
                then Fₕ.eval (a₁ x).1 ⟨2 * ((a₁ x).2 : ℝ), by { apply double_mem_I, convert h, norm_num }⟩
                else Gₕ.eval (a₁ x).1 ⟨2 * ((a₁ x).2 : ℝ) - 1, by { apply double_sub_one_mem_I (le_of_lt _), convert h, norm_num }⟩ : rfl
        ... = (Fₕ.hcomp Gₕ) (a₁ x) : (path.homotopy.hcomp_apply Fₕ Gₕ (a₁ x)).symm
        ... = Γ (a₁ x) : by rw Γ_def
        ... = (a₁.to_path.map Γ.continuous_to_fun) x : rfl
    -/
    have hr₂a₂ : r₂.toPath = a₂.toPath.map Γ.continuous_toFun := sorry
    /- TODO: Update to Lean4
      ext,
      have : 2⁻¹ ≤ ((a₂ x).2 : ℝ),
      {
        calc (2⁻¹ : ℝ) = ↑(γ T).2 : subtype.coe_inj.mpr hT_half.symm
                   ... ≤  ↑(a₂ x).2 : (directed_path_bounded a₂.dipath_to_path.2).1
      },
      calc r₂.to_path x = G ((a₂ x).1, ⟨2 * ((a₂ x).2 : ℝ) - 1, double_sub_one_mem_I this⟩) : rfl
            ... = if h : ((a₂ x).2 : ℝ) ≤ 1/2
                    then F ((a₂ x).1, ⟨2 * ((a₂ x).2 : ℝ), by { apply double_mem_I, convert h, norm_num }⟩)
                    else G ((a₂ x).1, ⟨2 * ((a₂ x).2 : ℝ) - 1,  by { apply double_sub_one_mem_I (le_of_lt _), convert h, norm_num }⟩) :
                      by {
                            split_ifs with h,
                            {
                              simp at h,
                              have ha₂x : ((a₂ x).2 : ℝ) = 2⁻¹ := by linarith,
                              simp [ha₂x],
                            },
                            refl,
                         }
            ... = if h : ((a₂ x).2 : ℝ) ≤ 1/2
                    then Fₕ.eval (a₂ x).1 ⟨2 * ((a₂ x).2 : ℝ), by { apply double_mem_I, convert h, norm_num }⟩
                    else Gₕ.eval (a₂ x).1 ⟨2 * ((a₂ x).2 : ℝ) - 1, by { apply double_sub_one_mem_I (le_of_lt _), convert h, norm_num }⟩ : rfl
            ... = (Fₕ.hcomp Gₕ) (a₂ x) : (path.homotopy.hcomp_apply Fₕ Gₕ (a₂ x)).symm
            ... = Γ (a₂ x) : by rw Γ_def
            ... = (a₂.to_path.map Γ.continuous_to_fun) x : rfl
    -/
    have : γ t = ((a₁.trans a₂).reparam φ φ₀ φ₁) t := sorry

    calc (Γ ∘ γ) t
      _ = Γ (γ t)
            := rfl
      _ = Γ (((a₁.trans a₂).reparam φ φ₀ φ₁) t)
            := by rw [this]
      _ = ((a₁.trans a₂).toPath.map Γ.continuous_toFun).reparam φ φ.continuous_toFun φ₀ φ₁ t
            := rfl
      _ = ((a₁.toPath.trans a₂.toPath).map Γ.continuous_toFun).reparam φ φ.continuous_toFun φ₀ φ₁ t
            := rfl
      _ = ((a₁.toPath.map Γ.continuous_toFun).trans (a₂.toPath.map Γ.continuous_toFun)).reparam φ φ.continuous_toFun φ₀ φ₁ t
            := by rw [Path.map_trans a₁.toPath a₂.toPath (Γ.continuous_toFun)]
      _ = (r₁.toPath.trans r₂.toPath).reparam φ φ.continuous_toFun φ₀ φ₁ t
            := by rw [hr₁a₁, hr₂a₂]
      _ = (r₁.trans r₂).reparam φ φ₀ φ₁ t
            := rfl
  exact hom_to_dihom Γ this

lemma hcomp_apply (F : Dihomotopy p₀ q₀) (G : Dihomotopy p₁ q₁) (x : I × I) :
    F.hcomp G x =
      if h : (x.2 : ℝ) ≤ 1/2 then
        F.eval x.1 ⟨2 * x.2, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨x.2.2.1, h⟩⟩
      else
        G.eval x.1 ⟨2 * x.2 - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, x.2.2.2⟩⟩ :=
  show ite _ _ _ = _ by split_ifs <;> exact Path.extend_extends _ _

lemma hcomp_half (F : Dihomotopy p₀ q₀) (G : Dihomotopy p₁ q₁) (t : I) :
    F.hcomp G (t, ⟨1/2, by norm_num, by norm_num⟩) = x₁ :=
  show ite _ _ _ = _ by norm_num

end

/--
Suppose `p` is a dipath, and `f g : D(I, I)` two monotonic subparametrizations. If `f` is dominated by `g`,
i.e. `∀ t, f t ≤ g t`, then we obtain a dihomotopy between the two subparametrization of `p` as
the interpolation between the two becomes directed.
-/
def reparam (p : Dipath x₀ x₁) (f : D(I, I)) (g : D(I, I)) (hf_le_g : ∀ (t : I), f t ≤ g t)
  (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) (hg₀ : g 0 = 0) (hg₁ : g 1 = 1) :
    Dihomotopy (p.reparam f hf₀ hf₁) (p.reparam g hg₀ hg₁) where
  toFun := p.comp (interpolate f g)
  map_zero_left := fun x => by { unfold interpolate; norm_num; rfl }
  map_one_left := fun x => by { unfold interpolate; norm_num; rfl }
  prop' := fun t x hx => by
    simp
    cases' hx with hx hx
    · have : g 0 = f 0 := hg₀.trans (hf₀.symm)
      rw [hx]
      constructor
      calc (p ((interpolate f g) (t, 0)))
        _ = p (f 0) := by rw [interpolate_constant_apply f g 0 (f 0) rfl this t]
      calc (p ((interpolate f g) (t, 0)))
        _ = p (g 0) := by rw [interpolate_constant_apply f g 0 (g 0) this.symm rfl t]
    · have : g 1 = f 1 := hg₁.trans (hf₁.symm)
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      constructor
      calc (p ((interpolate f g) (t, 1)))
        _ = p (f 1) := by rw [interpolate_constant_apply f g 1 (f 1) rfl this t]
      calc (p ((interpolate f g) (t, 1)))
        _ = p (g 1) := by rw [interpolate_constant_apply f g 1 (g 1) this.symm rfl t]
  directed_toFun := fun t₀ t₁ γ γ_dipath =>
    (p.toDirectedMap).directed_toFun (γ.map _) (directed_interpolate f g hf_le_g γ γ_dipath)


/--
For any `p : Dipath x₀ x₁`, there is a dihomotopy from `p` to `p.trans (Dipath.refl x₁)`.
-/
def trans_refl (p : Dipath x₀ x₁) : Dihomotopy p (p.trans (Dipath.refl x₁)) := by
  set f : D(I, I) := DirectedMap.id I
  set g : D(I, I) := TransReflReparamAuxMap
  have hf_le_g : ∀ (t : I), f t ≤ g t := by
    intro t
    simp [TransReflReparamAuxMap, Path.Homotopy.transReflReparamAux]
    apply Subtype.coe_le_coe.mp
    show (t : ℝ) ≤ ite ((t : ℝ) ≤ 2⁻¹) (2 * ↑t) 1
    split_ifs
    · have : 0 ≤ (t : ℝ) := t.2.1
      linarith
    · exact t.2.2
  convert reparam p f g hf_le_g (by simp) (by simp)
    (Subtype.ext Path.Homotopy.transReflReparamAux_zero)
    (Subtype.ext Path.Homotopy.transReflReparamAux_one)

  exact trans_refl_reparam_dipath p

/--
For any `p : Dipath x₀ x₁`, there is a dihomotopy from `(Dipath.refl x₀).trans p` to `p`.
-/
def refl_trans (p : Dipath x₀ x₁) : Dihomotopy ((Dipath.refl x₀).trans p) p := by
  set f : D(I, I) := ReflTransReparamAuxMap
  set g : D(I, I) := DirectedMap.id I
  have hf_le_g : ∀ (t : I), f t ≤ g t := fun t => by
    simp [ReflTransReparamAuxMap, ReflTransReparamAux]
    apply Subtype.coe_le_coe.mp
    show ite ((t : ℝ) ≤ 2⁻¹) 0 (2 * ↑t - 1) ≤ (t : ℝ)
    split_ifs
    · exact t.2.1
    · linarith [t.2.2]

  convert reparam p f g hf_le_g (Subtype.ext reflTransReparamAux_zero)
    (Subtype.ext reflTransReparamAux_one) (by simp) (by simp)
  exact refl_trans_reparam_dipath p

/--
For any `p : Dipath x₀ x₁`, there is a homotopy from `(Dipath.refl x₀).trans p` to `q.trans (Dipath.refl x₁)`,
where `q` is any directed reparametrization of `p`.
-/
def refl_trans_to_reparam_trans_refl (p : Dipath x₀ x₁) (f : D(I, I)) (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
    Dihomotopy ((Dipath.refl x₀).trans p) ((p.reparam f hf₀ hf₁).trans (Dipath.refl x₁)) := by
  set φ₁ : D(I, I) := ReflTransReparamAuxMap
  set φ₂ : D(I, I) := f.comp TransReflReparamAuxMap

  have hφ₁_le_φ₂ : ∀ (t : I), φ₁ t ≤ φ₂ t := by
    intro t
    simp [ReflTransReparamAuxMap, ReflTransReparamAux]
    simp [TransReflReparamAuxMap, Path.Homotopy.transReflReparamAux]
    apply Subtype.coe_le_coe.mp
    show ite ((t : ℝ) ≤ 2⁻¹) 0 (2 * (t : ℝ) - 1) ≤ (f ⟨ite ((t : ℝ) ≤ 2⁻¹) (2 * t : ℝ) 1, _⟩ : ℝ)
    by_cases h : (t : ℝ) ≤ 2⁻¹ <;> simp [h]
    · exact (f _).2.1
    · have : (t : ℝ) ≤ 1 := t.2.2
      simp [hf₁]
      linarith

  have hφ₂₀ : φ₂ 0 = 0 := by
    show f ⟨Path.Homotopy.transReflReparamAux 0, _⟩ = 0
    nth_rewrite 3 [←hf₀]
    congr
    exact Path.Homotopy.transReflReparamAux_zero

  have hφ₂₁ : φ₂ 1 = 1 := by
    show f ⟨Path.Homotopy.transReflReparamAux 1, _⟩ = 1
    nth_rewrite 3 [←hf₁]
    congr
    exact Path.Homotopy.transReflReparamAux_one

  convert reparam p φ₁ φ₂ hφ₁_le_φ₂ (Subtype.ext reflTransReparamAux_zero)
    (Subtype.ext reflTransReparamAux_one) hφ₂₀ hφ₂₁
  · exact refl_trans_reparam_dipath p
  · rw [trans_refl_reparam_dipath (p.reparam f hf₀ hf₁)]
    ext
    rfl


/--
Given `F : Dihomotopy p q`, and `f : D(X, Y)`, there is a dihomotopy from `p.map f` to
`q.map f` given by `f ∘ F`.
-/
@[simps!]
def map {p q : Dipath x₀ x₁} (F : Dihomotopy p q) (f : D(X, Y)) :
    Dihomotopy (p.map f) (q.map f) where
  toFun := f ∘ F
  map_zero_left := fun _ => by simp; rfl
  map_one_left := fun _ => by simp; rfl
  prop' := fun t x hx => by
    unfold DirectedMap.prod_const_fst DirectedMap.prod_map_mk

    cases' hx with hx hx

    case inr => sorry
      -- rw [Set.mem_singleton_iff _] at hx
      -- simp [hx]
      -- calc (f (F (t ,1))) = (f x₁) := by simp

    case inl => sorry
      -- simp [hx]
      -- calc (f (F (t ,0))) = (f x₀) := by simp


  directed_toFun := (f.comp F.toDirectedMap).directed_toFun

end Dihomotopy


section

variable (p₀ p₁ : Dipath x₀ x₁)
/--
Two dipaths `p₀` and `p₁` are `Dipath.PreDihomotopic` if there exists a `Dihomotopy` from `p₀` to `p₁`.
-/
def PreDihomotopic : Prop := Nonempty (Dihomotopy p₀ p₁)

/--
`Dipath.Dihomotopic` is the equivalence generated by `Dipath.PreDihomotopic`.
-/
def Dihomotopic : Prop := EqvGen PreDihomotopic p₀ p₁

end

namespace Dihomotopic

-- TODO: Remove if unnecessary?
lemma equivalence : Equivalence (@Dihomotopic X _ x₀ x₁) := by apply EqvGen.is_equivalence

/-- If `p` is dihomotopic with `q`, then `f ∘ p` is dihomotopic with `f ∘ q` for any directed map `f` -/
lemma map {p q : Dipath x₀ x₁} (h : p.Dihomotopic q) (f : D(X, Y)) :
    Dihomotopic (p.map f) (q.map f) :=
  EqvGen.rec
    (fun _ _ h => EqvGen.rel _ _ ⟨h.some.map f⟩)
    (fun x => EqvGen.refl (x.map f))
    (fun _ _ _ h => EqvGen.symm _ _ h)
    (fun _ _ _ _ _ h₁ h₂ => EqvGen.trans _ _ _ h₁ h₂)
  h

lemma hcomp_aid_left {p₀ p₁ : Dipath x₀ x₁} (q : Dipath x₁ x₂) (hp : p₀.Dihomotopic p₁) :
    (p₀.trans q).Dihomotopic (p₁.trans q) :=
  EqvGen.rec
    (fun _ _ h => EqvGen.rel _ _ ⟨h.some.hcomp (Dihomotopy.refl q)⟩)
    (fun p => EqvGen.refl (p.trans q))
    (fun _ _ _ h => EqvGen.symm _ _ h)
    (fun _ _ _ _ _ h₁ h₂ => EqvGen.trans _ _ _ h₁ h₂)
  hp

lemma hcomp_aid_right (p : Dipath x₀ x₁) {q₀ q₁ : Dipath x₁ x₂} (hq : q₀.Dihomotopic q₁) :
    (p.trans q₀).Dihomotopic (p.trans q₁) :=
  EqvGen.rec
    (fun _ _ h => EqvGen.rel _ _ ⟨(Dihomotopy.refl p).hcomp h.some⟩)
    (fun q => EqvGen.refl (p.trans q))
    (fun _ _ _ h => EqvGen.symm _ _ h)
    (fun _ _ _ _ _ h₁ h₂ => EqvGen.trans _ _ _ h₁ h₂)
  hq

/--
Suppose we have`p₀ p₁ : Dipath x₀ x₁` and `q₀ q₁ : Dipath x₁ x₂`.
If `p₀` is dihomotopic with `p₁` and `q₀` is dihomotopic with `q₁`,
then `p₀.trans q₀` is dihomotopic with `p₁.trans q₁`.
-/
lemma hcomp {p₀ p₁ : Dipath x₀ x₁} {q₀ q₁ : Dipath x₁ x₂} (hp : p₀.Dihomotopic p₁)
    (hq : q₀.Dihomotopic q₁) : (p₀.trans q₀).Dihomotopic (p₁.trans q₁) :=
  EqvGen.rec
    (fun p₀ p₁ hp₀_p₁ => by
      exact EqvGen.rec
          (fun _ _ hq₀_q₁ => EqvGen.rel _ _ ⟨hp₀_p₁.some.hcomp hq₀_q₁.some⟩)
          (fun q => EqvGen.rel _ _ ⟨hp₀_p₁.some.hcomp (Dihomotopy.refl q)⟩)
          (fun q₀ q₁ _ hp₀q₀_p₁q₁ => by
              have hp₀q₁_p₁q₂ := hcomp_aid_left q₁ (EqvGen.rel _ _ hp₀_p₁)
              have hp₁q₁_p₀q₀ := EqvGen.symm _ _ hp₀q₀_p₁q₁
              have hp₀q₀_p₁q₀ := hcomp_aid_left q₀ (EqvGen.rel _ _ hp₀_p₁)
              exact EqvGen.trans _ _ _ (EqvGen.trans _ _ _ hp₀q₁_p₁q₂ hp₁q₁_p₀q₀) hp₀q₀_p₁q₀
          )
          (fun q₀ q₁ q₂ hq₀_q₁ hq₁_q₂ _ _ => by
              have hp₀q₀_p₀q₁ := hcomp_aid_right p₀ hq₀_q₁
              have hp₀q₁_p₀q₂ := hcomp_aid_right p₀ hq₁_q₂
              have hp₀q₂_p₁q₂ := hcomp_aid_left q₂ (EqvGen.rel _ _ hp₀_p₁)
              exact EqvGen.trans _ _ _ (EqvGen.trans _ _ _ hp₀q₀_p₀q₁ hp₀q₁_p₀q₂) hp₀q₂_p₁q₂
          )
        hq
    )
    (fun p => by
      exact EqvGen.rec
          (fun _ _ h => hcomp_aid_right p (EqvGen.rel _ _ h))
          (fun q => EqvGen.refl (p.trans q))
          (fun _ _ _ h => EqvGen.symm _ _ h)
          (fun _ _ _ _ _ h₁ h₂ => EqvGen.trans _ _ _ h₁ h₂)
        hq
    )
    (fun p₀ p₁ hp₀_p₁ _ => by
      have hp₁_p₀ := EqvGen.symm _ _ hp₀_p₁
      exact EqvGen.rec
          (fun q₀ q₁ hq₀_q₁ => by
            have hp₁q₀_p₀q₀ := hcomp_aid_left q₀ hp₁_p₀
            have hp₀q₀_p₀q₁ := hcomp_aid_right p₀ (EqvGen.rel _ _ hq₀_q₁)
            exact EqvGen.trans _ _ _ hp₁q₀_p₀q₀ hp₀q₀_p₀q₁
          )
          (fun q => hcomp_aid_left q hp₁_p₀)
          (fun q₀ q₁ hq₀_q₁ _ => by
            have hp₁q₁_p₁q₀ := hcomp_aid_right p₁ (EqvGen.symm _ _ hq₀_q₁)
            have hp₁q₀_p₀q₀ := hcomp_aid_left q₀ (EqvGen.symm _ _ hp₀_p₁)
            exact EqvGen.trans _ _ _ hp₁q₁_p₁q₀ hp₁q₀_p₀q₀
          )
          (fun q₀ q₁ q₂ _ _ hp₁q₀_p₀q₁ hp₁q₁_p₀q₂ => by
            have hp₀q₁_p₁q₁ := hcomp_aid_left q₁ hp₀_p₁
            exact EqvGen.trans _ _ _ (EqvGen.trans _ _ _ hp₁q₀_p₀q₁ hp₀q₁_p₁q₁) hp₁q₁_p₀q₂
          )
        hq
    )
    (fun p₀ p₁ p₂ hp₀_p₁ hp₁_p₂ _ _ => by
      exact EqvGen.rec
          (fun q₀ q₁ hq₀_q₁ => by
            have hp₀q₁_p₁q₀ := hcomp_aid_left q₀ hp₀_p₁
            have hp₁q₀_p₂q₀ := hcomp_aid_left q₀ hp₁_p₂
            have hp₂q₀_p₂q₁ := hcomp_aid_right p₂ (EqvGen.rel _ _ hq₀_q₁)
            exact EqvGen.trans _ _ _ (EqvGen.trans _ _ _ hp₀q₁_p₁q₀ hp₁q₀_p₂q₀) hp₂q₀_p₂q₁
          )
          (fun q => by
            have hp₀q_p₁q := hcomp_aid_left q hp₀_p₁
            have hp₁q_p₂q := hcomp_aid_left q hp₁_p₂
            exact EqvGen.trans _ _ _ hp₀q_p₁q hp₁q_p₂q
          )
          (fun q₀ q₁ hq₀_q₁ hp₀q₀_p₂q₁ => by
            have hq₁_q₀ := EqvGen.symm _ _ hq₀_q₁
            have hp₀q₁_p₀q₀ := hcomp_aid_right p₀ hq₁_q₀
            have hp₂q₁_p₂q₀ := hcomp_aid_right p₂ hq₁_q₀
            exact EqvGen.trans _ _ _ (EqvGen.trans _ _ _ hp₀q₁_p₀q₀ hp₀q₀_p₂q₁) hp₂q₁_p₂q₀
          )
          (fun q₀ q₁ q₂ _ _ hp₀q₀_p₂q₁ hp₀q₁_p₂q₂ => by
            have hp₂_p₀ := EqvGen.symm _ _ (EqvGen.trans _ _ _ hp₀_p₁ hp₁_p₂)
            have hp₂q₂_p₀q₁ := hcomp_aid_left q₁ hp₂_p₀
            exact EqvGen.trans _ _ _ (EqvGen.trans _ _ _ hp₀q₀_p₂q₁ hp₂q₂_p₀q₁) hp₀q₁_p₂q₂
          )
        hq
    )
  hp

/--
If `p` is a dipath, then it is dihomotopic with any monotonic subparametrization.
-/
lemma reparam (p : Dipath x₀ x₁) (f : D(I, I)) (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
  p.Dihomotopic (p.reparam f hf₀ hf₁) := by

  set p' := p.reparam f hf₀ hf₁
  set p₁ := ((refl x₀).trans p)
  set p₂ := (p'.trans (refl x₁))

  have h₁ : p₁.PreDihomotopic p := ⟨Dihomotopy.refl_trans p⟩
  have h₂ : p₁.PreDihomotopic p₂ := ⟨Dihomotopy.refl_trans_to_reparam_trans_refl p f hf₀ hf₁⟩
  have h₃ : p'.PreDihomotopic p₂ := ⟨Dihomotopy.trans_refl p'⟩

  have h₁ : p.Dihomotopic p₁ := EqvGen.symm _ _ (EqvGen.rel _ _ h₁)
  have h₂ : p₁.Dihomotopic p₂ := EqvGen.rel _ _ h₂
  have h₃ : p₂.Dihomotopic p' := EqvGen.symm _ _ (EqvGen.rel _ _ h₃)

  exact EqvGen.trans _ _ _ (EqvGen.trans _ _ _ h₁ h₂) h₃

/--
The setoid on `Dipath`s defined by the equivalence relation `Dipath.Dihomotopic`. That is, two paths are
equivalent if there is a chain of `Dihomotopies` starting in one and ending in the other.
-/
protected def setoid (x₀ x₁ : X) : Setoid (Dipath x₀ x₁) := ⟨Dihomotopic, equivalence⟩

/--
The quotient on `Dipath x₀ x₁` by the equivalence relation `Dipath.Dihomotopic`.
-/
protected def Quotient (x₀ x₁ : X) := Quotient (Dihomotopic.setoid x₀ x₁)

attribute [local instance] Dihomotopic.setoid

-- TODO: Is this right?
instance : Inhabited (Dihomotopic.Quotient x₀ x₀) :=
  ⟨Quotient.mk' <| Dipath.refl x₀⟩

/- The composition of dipath dihomotopy classes. This is `Dipath.trans` descended to the quotient. -/
def Quotient.comp (P₀ : Dipath.Dihomotopic.Quotient x₀ x₁) (P₁ : Dipath.Dihomotopic.Quotient x₁ x₂) :
  Dipath.Dihomotopic.Quotient x₀ x₂ :=
Quotient.map₂ Dipath.trans (fun (_ : Dipath x₀ x₁) _ hp (_ : Dipath x₁ x₂) _ hq => (hcomp hp hq)) P₀ P₁

lemma comp_lift (P₀ : Dipath x₀ x₁) (P₁ : Dipath x₁ x₂) : ⟦P₀.trans P₁⟧ = Quotient.comp ⟦P₀⟧ ⟦P₁⟧ := rfl

/- The image of a dipath dihomotopy class `P₀` under a directed map `f`.
    This is `Dipath.map` descended to the quotient -/
def Quotient.map_fn (P₀ : Dipath.Dihomotopic.Quotient x₀ x₁) (f : D(X, Y)) :
  Dipath.Dihomotopic.Quotient (f x₀) (f x₁) :=
Quotient.map (fun (q : Dipath x₀ x₁) => q.map f) (fun _ _ h => Dipath.Dihomotopic.map h f) P₀

lemma map_lift (P₀ : Dipath x₀ x₁) (f : D(X, Y)) :
  ⟦P₀.map f⟧ = Quotient.map_fn ⟦P₀⟧ f := rfl

lemma quot_reparam (γ : Dipath x₀ x₁) {f : D(I, I)} (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
    @Eq (Dipath.Dihomotopic.Quotient _ _) ⟦γ.reparam f hf₀ hf₁⟧ ⟦γ⟧ := by
  symm
  exact Quotient.eq.mpr (Dipath.Dihomotopic.reparam γ f hf₀ hf₁)

lemma hpath_hext {p₁ : Dipath x₀ x₁} {p₂ : Dipath x₂ x₃} (hp : ∀ t, p₁ t = p₂ t) :
    @HEq (Dipath.Dihomotopic.Quotient _ _) ⟦p₁⟧ (Dipath.Dihomotopic.Quotient _ _) ⟦p₂⟧ := by
  obtain rfl : x₀ = x₂ := by convert hp 0 <;> simp
  obtain rfl : x₁ = x₃ := by convert hp 1 <;> simp
  rw [heq_iff_eq]
  congr
  ext t
  exact hp t

end Dihomotopic

end Dipath

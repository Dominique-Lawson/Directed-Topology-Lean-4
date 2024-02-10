import Lean4.directed_unit_interval

/-
  This file contains the definition of a dipath in a directed space:
  A path between two points paired with the proof that it is a dipath.
  The following dipath constructions are given:
  * refl : the constant dipath
  * trans : the concatenation of dipaths
  * map : the image of a dipath under a directed map
  * subparam : the monotonic subparametrization of a dipath

  This file follows the structure of https://github.com/leanprover-community/mathlib/blob/master/src/topology/path_connected.lean
-/

noncomputable section

open DirectedMap Set
open scoped unitInterval

universe u
variable {X : Type u} [DirectedSpace X] {x y z : X}

/-- A dipath is a path together with a proof that that path "is a dipath" -/
structure Dipath (x y : X) extends Path x y :=
  (dipath_toPath : IsDipath toPath)

-- TODO: Fix or remove? PathConnected.lean from Mathlib4 does not have the first Coercion
instance : CoeFun (Dipath x y) (fun _ => I → X) := ⟨fun γ => γ.toFun⟩
-- instance : Coe (Dipath x y) (C(I, X)) := ⟨fun γ => γ.toContinuousMap⟩
instance : Coe (Dipath x y) (Path x y) := ⟨fun γ => γ.toPath⟩

namespace Dipath

lemma directed (γ : Dipath x y) : DirectedMap.Directed γ.toContinuousMap :=
  fun _ _ _ φ_dipath => isDipath_reparam φ_dipath γ.dipath_toPath

def toDirectedMap (γ : Dipath x y) : D(I, X) where
  directed_toFun := Dipath.directed γ
  toFun := γ.toFun

-- TODO: Remove or add depending on necessary somewhere else.
/-- To bypass the conversion to continuous_map -/
-- def to_fun : (Dipath x y) → I → X := fun f => f.toFun

instance Dipath.instFunLike : FunLike (Dipath x y) I X where
  coe := fun γ => γ.toFun
  coe_injective' := fun γ γ' h => by
    obtain ⟨⟨⟨_, _⟩, _, _⟩, _⟩ := γ
    obtain ⟨⟨⟨_, _⟩, _, _⟩, _⟩ := γ'
    congr

instance Dipath.directedMapClass : DirectedMapClass (Dipath x y) I X where
  map_continuous := fun γ => γ.continuous_toFun
  map_directed := fun γ => directed γ

end Dipath

-- TODO: Fix: Problem with out-params
-- instance : Coe (Dipath x y) (D(I, X)) := ⟨fun γ => γ.toDirectedMap⟩

@[ext]
protected lemma Dipath.ext : ∀ {γ₁ γ₂ : Dipath x y}, (γ₁ : I → X) = γ₂ → γ₁ = γ₂ := by
  rintro ⟨⟨⟨x, h10⟩, h11, h12⟩, h13⟩ ⟨⟨⟨y, h20⟩, h21, h22⟩, h23⟩ rfl
  rfl

namespace Dipath

def of_isDipath {γ : Path x y} (hγ :IsDipath γ) : Dipath x y := {
  toPath := γ,
  dipath_toPath := hγ,
}

/-- An directed map from I to a directed space can be turned into a dipath -/
def of_directedMap (f : D(I, X)) : Dipath (f 0) (f 1) := {
  toContinuousMap := (f : C(I, X)),
  source' := by simp,
  target' := by simp,
  dipath_toPath := DirectedUnitInterval.isDipath_of_isDipath_comp_id
    $ f.directed_toFun DirectedUnitInterval.IdentityPath DirectedUnitInterval.isDipath_identityPath
}

@[simp] lemma coe_mk (f : I → X) (h₀ h₁ h₂ h₃) : ⇑(mk ⟨⟨f, h₀⟩, h₁, h₂⟩ h₃ : Dipath x y) = f := rfl

variable (γ : Dipath x y)

@[continuity]
protected lemma continuous : Continuous γ :=
  γ.continuous_toFun

@[simp] protected lemma source : γ 0 = x :=
  γ.source'

@[simp] protected lemma target : γ 1 = y :=
  γ.target'

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
because it is a composition of multiple projections. -/
def simps.apply : I → X :=
  γ

-- TODO: Verify that this is correct (see PathConnected.lean)
initialize_simps_projections Dipath (toFun → simps.apply, -toContinuousMap)

@[simp]
lemma coe_toContinuousMap : ⇑γ.toContinuousMap = γ := rfl
@[simp]
lemma coe_toDirectedMap : ⇑γ.toDirectedMap = γ := rfl

-- TODO: Is this necessary? (see PathConnected.lean) Is this different from coe_mk above?
-- @[simp]
-- theorem coe_mk : ⇑(γ : C(I, X)) = γ := rfl

/-- Any function `φ : Π (a : α), dipath (x a) (y a)` can be seen as a function `α × I → X`. -/
instance hasUncurryDipath {X α : Type*} [DirectedSpace X] {x y : α → X} :
  Function.HasUncurry (∀ a : α, Dipath (x a) (y a)) (α × I) X :=
⟨fun φ p => φ p.1 p.2⟩


/-! ### Properites about the range of dipaths -/

@[simp] lemma coe_range (γ : Dipath x y) : range γ = range γ.toPath := rfl
@[simp] lemma range_eq_image (γ : Dipath x y) : range γ = γ.extend '' I :=
  Set.ext (fun z =>
    ⟨fun ⟨t, ht⟩ => mem_image_iff_bex.mpr ⟨t, ⟨t.2, by { simp; exact ht }⟩⟩,
    fun ⟨t, t_mem_I, ht⟩ => ⟨⟨t, t_mem_I⟩, by {
      rw [ht.symm, Path.extend_extends γ.toPath t_mem_I]
      rfl
    }⟩⟩
  )

@[simp] lemma range_eq_image_I (γ : Dipath x y) : range γ = γ '' Icc 0 1 :=
  Set.ext (fun _ =>
    ⟨fun ⟨t, ht⟩ => mem_image_iff_bex.mpr ⟨t, ⟨t.2, ht⟩⟩,
    fun ⟨t, t_mem_I, ht⟩ => ⟨⟨t, t_mem_I⟩, ht⟩⟩
  )

lemma image_extend_eq_image (γ : Dipath x y) (a b : I) : γ.extend '' Icc ↑a ↑b = γ '' Icc a b := by
  ext y
  constructor
  {
    rintro ⟨t, t_ab, ht⟩
    use ⟨t, ⟨le_trans a.2.1 t_ab.1, le_trans t_ab.2 b.2.2⟩⟩
    rw [←ht, Path.extend_extends γ.toPath _]
    refine ⟨t_ab, rfl⟩
  }
  {
    rintro ⟨t, t_ab, ht⟩
    use t
    constructor
    exact t_ab
    rw [← ht]
    convert Path.extend_extends γ.toPath ⟨le_trans a.2.1 t_ab.1, le_trans t_ab.2 b.2.2⟩
  }

/-! ### Reflexive dipaths -/

-- TODO: Why is simps! suggested instead of simps?
/-- The constant dipath from a point to itself -/
@[refl, simps!] def refl (x : X) : Dipath x x := {
  Path.refl x with
  dipath_toPath := isDipath_constant x
}

@[simp] lemma refl_range {a : X} : range (Dipath.refl a) = {a} := Path.refl_range

/-! ### Concatenation of dipaths -/

/-- Directed paths can be concatenated -/
@[trans] def trans (γ : Dipath x y) (γ' : Dipath y z) : Dipath x z :=
{
  γ.toPath.trans γ'.toPath with
  dipath_toPath := isDipath_concat γ.dipath_toPath γ'.dipath_toPath
}

@[simp] lemma trans_to_path (γ : Dipath x y) (γ' : Dipath y z) :
  γ.toPath.trans γ'.toPath = (γ.trans γ').toPath := by
  ext t
  rfl

lemma trans_apply (γ : Dipath x y) (γ' : Dipath y z) (t : I) : (γ.trans γ') t =
  if h : (t : ℝ) ≤ 1/2 then
    γ ⟨2 * t, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, h⟩⟩
  else
    γ' ⟨2 * t - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, t.2.2⟩⟩ :=
Path.trans_apply (γ.toPath) (γ'.toPath) t

lemma trans_range (γ : Dipath x y) (γ' : Dipath y z) : range (γ.trans γ') = range γ ∪ range γ' :=
  Path.trans_range γ.toPath γ'.toPath

-- TODO: First add (rewritten) fractions
-- lemma trans_eval_at_half (γ : Dipath x y) (γ' : Dipath y z) :
--   (γ.trans γ') (auxiliary.inv_I two_pos) = y :=
-- begin
--   rw dipath.trans_apply,
--   simp,
-- end

/-! ### Mapping dipaths -/

/-- Image of a dipath from `x` to `y` by a directed map -/
def map (γ : Dipath x y) {Y : Type*} [DirectedSpace Y] (f : D(X, Y)) : Dipath (f x) (f y) :=
{
  γ.toPath.map f.continuous_toFun with
  dipath_toPath := f.directed_toFun γ.toPath γ.dipath_toPath,
}

@[simp] lemma map_coe (γ : Dipath x y) {Y : Type*} [DirectedSpace Y] (f : D(X, Y)) :
  (γ.map f : I → Y) = f ∘ γ :=
by { ext t; rfl }

@[simp] lemma map_trans (γ : Dipath x y) (γ' : Dipath y z) {Y : Type*} [DirectedSpace Y] (f : D(X, Y)) :
  (γ.trans γ').map f = (γ.map f).trans (γ'.map f) := by
  ext t
  rw [trans_apply, map_coe, Function.comp_apply, trans_apply]
  simp
  split_ifs <;> rfl

@[simp] lemma map_id (γ : Dipath x y) : γ.map (DirectedMap.id X) = γ := by { ext; rfl }

@[simp] lemma map_map (γ : Dipath x y) {Y : Type*} [DirectedSpace Y] {Z : Type*} [DirectedSpace Z]
  (f : D(X, Y)) (g : D(Y, Z)) : (γ.map f).map g = γ.map (g.comp f) := by { ext; rfl }

/-! ### Casting dipaths -/

/-- Casting a dipath from `x` to `y` to a dipath from `x'` to `y'` when `x' = x` and `y' = y` -/
def cast (γ : Dipath x y) {x' y'} (hx : x' = x) (hy : y' = y) : Dipath x' y' :=
{ toFun := γ,
  continuous_toFun := γ.continuous,
  dipath_toPath := isDipath_cast γ.toPath hx hy γ.dipath_toPath,
  source' := by simp [hx],
  target' := by simp [hy]
}

lemma cast_apply (γ : Dipath x y) {x' y'} (hx : x' = x) (hy : y' = y) (t : I):
  (γ.cast hx hy) t = γ t := rfl

@[simp] lemma trans_cast {X : Type*} [DirectedSpace X] {a₁ a₂ b₁ b₂ c₁ c₂ : X}
  (γ : Dipath a₂ b₂) (γ' : Dipath b₂ c₂) (ha : a₁ = a₂) (hb : b₁ = b₂) (hc : c₁ = c₂) :
  (γ.cast ha hb).trans (γ'.cast hb hc) = (γ.trans γ').cast ha hc := rfl

@[simp] lemma cast_coe (γ : Dipath x y) {x' y'} (hx : x' = x) (hy : y' = y) :
  (γ.cast hx hy : I → X) = γ := rfl

lemma cast_range (γ : Dipath x y) {x' y'} (hx : x' = x) (hy : y' = y) :
  range (γ.cast hx hy) = range γ := rfl

lemma cast_image (γ : Dipath x y) {x' y'} (hx : x' = x) (hy : y' = y) (a b : ℝ) :
  (γ.cast hx hy).extend '' Icc a b = γ.extend '' Icc a b := rfl

lemma dipath_of_directed_map_of_to_dimap (γ : Dipath x y) :
  Dipath.of_directedMap (γ.toDirectedMap) = γ.cast γ.source' γ.target' := by {ext t; rfl }

/-! ### Reparametrising a path -/

def subparam (γ : Dipath x y) (f : D(I, I)) : Dipath (γ (f 0)) (γ (f 1)) :=
{
  toFun := γ ∘ f
  continuous_toFun := by continuity
  source' := rfl
  target' := rfl
  dipath_toPath := by
      set p : Path (f 0) (f 1) :=
        { toFun := f,
          continuous_toFun := f.continuous_toFun,
          source' := rfl,
          target' := rfl
        }
      have p_mono : Monotone p := DirectedUnitInterval.monotone_of_directed f
      exact isDipath_reparam p_mono γ.dipath_toPath
}

lemma subparam_range (γ : Dipath x y) (f : D(I, I)) :
  range (γ.subparam f) ⊆ range γ := fun _ ⟨a, ha⟩ => ⟨f a, ha⟩

/--
Given a dipath `γ` and a dimap `f : I → I` where `f 0 = 0` and `f 1 = 1`, `γ.reparam f` is the
dipath defined by `γ ∘ f`.
-/
def reparam (γ : Dipath x y) (f : D(I, I)) (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
  Dipath x y :=
(subparam γ f).cast (hf₀.symm ▸ γ.source.symm) (hf₁.symm ▸ γ.target.symm)

@[simp]
lemma coe_to_fun (γ : Dipath x y) (f : D(I, I)) (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
  ⇑(γ.reparam f hf₀ hf₁) = γ ∘ f := rfl

@[simp]
lemma reparam_id (γ : Dipath x y) : γ.reparam (DirectedMap.id I) rfl rfl = γ :=
by { ext; rfl }

lemma range_reparam (γ : Dipath x y) (f : D(I, I)) (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
  range (γ.reparam f hf₀ hf₁) = range γ :=
Path.range_reparam γ.toPath f.continuous_toFun hf₀ hf₁

variable {Y : Type*} [DirectedSpace Y] {x₀ x₁ : X} {y₀ y₁ : Y}

/-- Two dipaths together form a dipath in the product space -/
def dipath_product (γ₁ : Dipath x₀ x₁) (γ₂ : Dipath y₀ y₁) : Dipath (x₀, y₀) (x₁, y₁) where
  toFun := fun t => (γ₁ t, γ₂ t)
  source' := by { simp [γ₁.source', γ₂.source'] }
  target' := by { simp [γ₁.target', γ₂.target'] }
  dipath_toPath := by
      constructor
      { convert γ₁.dipath_toPath }
      { convert γ₂.dipath_toPath }

end Dipath

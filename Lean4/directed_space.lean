import Mathlib.Topology.Connected.PathConnected

/-
  # Definition of directed spaces
  This file defines the directed space, an extension of a topological space where
  some of its paths are considered directed paths.
-/

universe u

open scoped unitInterval

/-- Definition of a directed topological space.

    Dipaths are closed under:
    * Constant paths,
    * Concatenation of paths,
    * Monotone reparametrization of paths
 -/
class DirectedSpace (α : Type u) extends TopologicalSpace α where
  IsDipath : ∀ {x y : α}, Path x y → Prop
  isDipath_constant : ∀ (x : α), IsDipath (Path.refl x)
  isDipath_concat : ∀ {x y z : α} {γ₁ : Path x y} {γ₂ : Path y z}, IsDipath γ₁ → IsDipath γ₂ → IsDipath (Path.trans γ₁ γ₂)
  isDipath_reparam : ∀ {x y : α} {γ : Path x y} {t₀ t₁ : I} {f : Path t₀ t₁}, Monotone f → IsDipath γ → IsDipath (f.map (γ.continuous_toFun))

section DirectedSpace

variable {α : Type u} {x y z : α} [DirectedSpace α] {γ : Path x y}  {γ' : Path y z} {t₀ t₁ : I} {f : Path t₀ t₁}

def IsDipath : (Path x y) → Prop :=
  DirectedSpace.IsDipath

def isDipath_constant (x : α) : IsDipath (Path.refl x) :=
  DirectedSpace.isDipath_constant _

def isDipath_concat (hγ : IsDipath γ) (hγ' : IsDipath γ') : IsDipath (γ.trans γ') :=
  DirectedSpace.isDipath_concat hγ hγ'

def isDipath_reparam (hfmono : Monotone f) (hγ : IsDipath γ) : IsDipath (f.map γ.continuous_toFun) :=
  DirectedSpace.isDipath_reparam hfmono hγ

/-- Casting a path that is directed into another path gives another directed path -/
lemma is_dipath_cast {x y x' y' : α} (γ : Path x y) (hx : x' = x) (hy : y' = y) (hγ : IsDipath γ) :
  IsDipath (γ.cast hx hy) := by
    subst_vars
    convert hγ

end DirectedSpace

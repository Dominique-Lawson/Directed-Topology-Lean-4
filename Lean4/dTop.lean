import Lean4.constructions
import Mathlib.CategoryTheory.ConcreteCategory.BundledHom
import Mathlib.CategoryTheory.Elementwise

/-
  This file contains the definition of `dTopCat`, the category of directed spaces.
  The structure of this file is based on the approach for the undirected version in Mathlib:
  https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Topology/Category/TopCat/Basic.lean
-/

open DirectedMap
open CategoryTheory

universe u

@[to_additive existing dTopCat]
def dTopCat : Type (u+1) := Bundled DirectedSpace

namespace dTopCat

-- TODO: For some reason, @DirectedMap.toFun does not work as the first argument
instance bundledHom : BundledHom @DirectedMap :=
 ⟨fun _ _ f => f.toFun, @DirectedMap.id, @DirectedMap.comp, @DirectedMap.coe_injective,
  fun _ => rfl, fun _ _ _ _ _ => rfl⟩

deriving instance LargeCategory for dTopCat

instance concreteCategory : ConcreteCategory dTopCat := by
  dsimp [dTopCat]
  infer_instance

instance instCoeSortdTopCatType: CoeSort dTopCat Type* := Bundled.coeSort

instance directedSpaceUnbundled (x : dTopCat) : DirectedSpace x := x.str

attribute [instance] ConcreteCategory.instFunLike in
instance (X Y : dTopCat.{u}) : CoeFun (X ⟶ Y) fun _ => X → Y where
  coe f := f

lemma id_app (X : dTopCat.{u}) (x : ↑X) : (𝟙 X : X → X) x = x := rfl

lemma comp_app {X Y Z : dTopCat.{u}}  (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
  (f ≫ g : X → Z) x = g (f x) := rfl

/-- Construct a bundled `dTopCat` from the underlying type and the typeclass. -/
def of (X : Type u) [DirectedSpace X] : dTopCat := ⟨X, inferInstance⟩

instance directedSpace_coe (X : dTopCat) : DirectedSpace X := X.str

@[reducible]
instance directedSpace_forget (X : dTopCat) : DirectedSpace <| (forget dTopCat).obj X := X.str

@[simp]
lemma coe_of (X : Type u) [DirectedSpace X] : (of X : Type u) = X := rfl

instance subspace_coe {X : dTopCat} : CoeTC (Set X) dTopCat := ⟨fun s => dTopCat.of s⟩

def DirectedSubtypeHom {X : dTopCat} (Y : Set X) : (dTopCat.of Y) ⟶ X :=
  DirectedSubtypeInclusion (fun s => s ∈ Y)
def DirectedSubsetHom {X : dTopCat} {Y₀ Y₁ : Set X} (h : Y₀ ⊆ Y₁) : (dTopCat.of Y₀) ⟶ Y₁ :=
  DirectedSubsetInclusion h

end dTopCat

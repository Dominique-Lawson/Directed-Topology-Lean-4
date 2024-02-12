import Lean4.fundamental_category
import Lean4.dihomotopy_flip

/-
  This file contains the construction of the following statement:

  Let a dihomotopy `F : f ~ g`, with `f g : D(I, X)` be  given:
   C----- g -----D
   |             |
   |             |
   |             |
   |             |
   A----- f -----B
  Then there is a path-dihomotopy between the paths
    A --refl A--> A --f--> B --F.eval_at_right 1--> D
  and
    A --F.eval_at_right 0--> C --g--> D --refl D--> D
-/

universe u

open DirectedMap
open scoped unitInterval

noncomputable section

namespace DirectedMap
namespace Dihomotopy

variable {X : dTopCat} {x y : X} (γ : Dipath x y)

def MinDirected : D(I × I, I) where
  toFun := fun t => min t.1 t.2
  directed_toFun := fun t₀ t₁ γ ⟨h₁, h₂⟩ a b hab => le_min (min_le_of_left_le (h₁ hab)) (min_le_of_right_le (h₂ hab))

def MaxDirected : D(I × I, I) where
  toFun := fun t => max t.1 t.2
  directed_toFun := fun t₀ t₁ γ ⟨h₁, h₂⟩ a b hab => max_le (le_max_of_le_left (h₁ hab)) (le_max_of_le_right (h₂ hab))

def SourceToPath : Dihomotopy (Dipath.refl x).toDirectedMap γ.toDirectedMap where
  toDirectedMap := γ.toDirectedMap.comp MinDirected
  map_zero_left := fun t => by
    show γ (min 0 t) = _
    have : min 0 t = 0 := min_eq_left t.2.1
    rw [this, γ.source]
    rfl
  map_one_left := fun t => by
    show γ (min 1 t) = _
    have : min 1 t = t := min_eq_right t.2.2
    rw [this]
    rfl

lemma sourceToPath_apply (s t : I) : SourceToPath γ (s, t) = γ (min s t) := rfl

lemma sourceToPath_range : Set.range (SourceToPath γ) = Set.range γ := by
  ext z
  constructor
  · intro ⟨t, ht⟩
    use min t.1 t.2
    rw [←ht]
    exact (sourceToPath_apply γ t.1 t.2).symm
  · intro ⟨t, ht⟩
    use (t, t)
    rw [←ht, sourceToPath_apply]
    exact congr_arg γ (min_self t)

def PathToTarget : Dihomotopy γ.toDirectedMap (Dipath.refl y).toDirectedMap where
  toDirectedMap := γ.toDirectedMap.comp MaxDirected
  map_zero_left := fun t => by
    show γ (max 0 t) = _
    have : max 0 t = t := max_eq_right t.2.1
    rw [this]
    rfl
  map_one_left := fun t => by
    show γ (max 1 t) = _
    have : max 1 t = 1 := max_eq_left t.2.2
    rw [this, γ.target]
    rfl

lemma pathToTarget_apply (s t : I) : PathToTarget γ (s, t) = γ (max s t) := rfl

lemma pathToTarget_range : Set.range (PathToTarget γ) = Set.range γ := by
  ext z
  constructor
  · rintro ⟨t, ht⟩
    use max t.1 t.2
    rw [←ht]
    exact (pathToTarget_apply γ t.1 t.2).symm
  · rintro ⟨t, ht⟩
    use (t, t)
    rw [←ht, pathToTarget_apply]
    exact congr_arg γ (max_self t)

end Dihomotopy
end DirectedMap

namespace DihomToPathDihom

variable {X : dTopCat} {f g : D(I, X)}

def dihom_to_dihom_of_paths (F : Dihomotopy f g) :
    Dihomotopy (Dipath.of_directedMap f).toDirectedMap (Dipath.of_directedMap g).toDirectedMap where
  toDirectedMap := F.toDirectedMap
  map_zero_left := fun x => by rw [F.map_zero_left]; rfl
  map_one_left := fun x => by rw [F.map_one_left]; rfl

/--
  Let a dihomotopy `F : f ~ g`, with `f g : D(I, X)` be  given:
    C----- g -----D
    |             |
    |             |
    |             |
    |             |
    A----- f -----B
  Then there is a path-dihomotopy between the paths
    A --refl A--> A --f--> B --F.eval_at_right 1--> D
  and
    A --F.eval_at_right 0--> C --g--> D --refl D--> D
-/
def dihom_to_path_dihom (F : Dihomotopy f g) : Dipath.Dihomotopy
    (((Dipath.refl (f 0)).trans (Dipath.of_directedMap f)).trans (F.eval_at_right 1))
    (((F.eval_at_right 0).trans (Dipath.of_directedMap g)).trans (Dipath.refl (g 1))) where
  toDihomotopy :=
      Dihomotopy.hcomp'
      (
      Dihomotopy.hcomp'
        (DirectedMap.Dihomotopy.SourceToPath (F.eval_at_right 0))
        (dihom_to_dihom_of_paths F)
        (by
          ext s
          show F ((min s 1), 0) = F (s, 0)
          rw [min_eq_left]
          exact s.2.2
        )
      )
      (DirectedMap.Dihomotopy.PathToTarget (F.eval_at_right 1))
      (
        by
          ext s
          show (Dihomotopy.hcomp' _ _ _) (s, 1) = _
          rw [Dihomotopy.hcomp'_apply_one_right]
          show F (s, _ ) = F ((max s 0), 1)
          rw [max_eq_left]
          exact s.2.1
      )
  prop' := fun t x hx => by
    cases hx
    case inl hx => -- x = 0
      subst hx
      constructor <;> {
        show (Dihomotopy.hcomp' _ _ _) (t, 0) = _
        rw [Dihomotopy.hcomp'_apply_zero_right]
        rw [Dihomotopy.hcomp'_apply_zero_right]
        simp
        show F (min t 0, 0) = f 0
        rw [min_eq_right]
        simp
        exact t.2.1
      }
    case inr hx =>
      rw [Set.mem_singleton_iff] at hx
      subst hx
      constructor <;> {
        show (Dihomotopy.hcomp' _ _ _) (t, 1) = _
        rw [Dihomotopy.hcomp'_apply_one_right]
        simp
        show F (max t 1, 1) = g 1
        rw [max_eq_right]
        simp
        exact t.2.2
      }


lemma dihom_to_path_dihom_range (F : Dihomotopy f g) :
    Set.range (dihom_to_path_dihom F) ⊆ Set.range F := by
  unfold dihom_to_path_dihom
  let A := DirectedMap.Dihomotopy.SourceToPath (F.eval_at_right 0)
  let B := dihom_to_dihom_of_paths F
  let C := DirectedMap.Dihomotopy.PathToTarget (F.eval_at_right 1)

  have hA : Set.range A ⊆ Set.range F := by
    dsimp [A]
    rw [DirectedMap.Dihomotopy.sourceToPath_range]
    rintro x ⟨t, ht⟩
    use (t, 0)
    exact ht

  have hB : Set.range B ⊆ Set.range F := fun x h => h
  have hC : Set.range C ⊆ Set.range F := by
    dsimp [C]
    rw [DirectedMap.Dihomotopy.pathToTarget_range]
    rintro x ⟨t, ht⟩
    use (t, 1)
    exact ht

  apply subset_trans (Dihomotopy.hcomp'_range (A.hcomp' B _) C _) (Set.union_subset ?_ hC)
  exact subset_trans (Dihomotopy.hcomp'_range A B _) (Set.union_subset hA hB)

end DihomToPathDihom

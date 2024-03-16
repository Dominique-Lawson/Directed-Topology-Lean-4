import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Homotopy.Basic

/-
  This file contains lemmas about monotone paths in a preordered topological space
-/

open scoped unitInterval

lemma monotone_path_bounded_left {α : Type*} {x y : α} [TopologicalSpace α] [Preorder α]
  {γ : Path x y} (hγ : Monotone γ) (t : I) : x ≤ γ t :=
    Eq.trans_le (id γ.source.symm) (hγ unitInterval.nonneg')

lemma monotone_path_bounded_right {α : Type*} {x y : α} [TopologicalSpace α] [Preorder α]
  {γ : Path x y} (hγ : Monotone γ) (t : I) : γ t ≤ y :=
    Eq.trans_ge (id γ.target) (hγ (unitInterval.le_one t))

lemma monotone_path_bounded {α : Type*} {x y : α} [TopologicalSpace α] [Preorder α]
  {γ : Path x y} (hγ : Monotone γ) (t : I) : x ≤ γ t ∧ γ t ≤ y :=
  ⟨monotone_path_bounded_left hγ t, monotone_path_bounded_right hγ t⟩

lemma monotone_path_source_le_target {α : Type*} {x y : α} [TopologicalSpace α] [Preorder α]
  {γ : Path x y} (hγ : Monotone γ) : x ≤ y :=
  Eq.trans_le (id γ.source.symm) (Eq.trans_ge (id γ.target) (hγ unitInterval.nonneg'))

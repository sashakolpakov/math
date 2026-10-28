/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
This file has been modified.
-/
import Mathlib.Topology.Sheaves.Points

/-! # Points -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.LargeZariski.Points.LargeZariskiPoints

noncomputable section

/-!
# Zariski points at the native coefficient universe

The points are the actual scheme points. Their membership fibers are
lifted only to match the original crystalline module universe. They
form a conservative family on the original lattice of open subsets.
-/

open _root_.CategoryTheory GrothendieckTopology _root_.TopologicalSpace

universe u

variable {X : Type u} [TopologicalSpace X]

def point (x : X) : Point.{u + 1} (Opens.grothendieckTopology X) where
  fiber.obj U := ULift.{u + 1} (PLift (x ∈ U))
  fiber.map f := ↾fun h => ⟨⟨leOfHom f h.down.down⟩⟩
  isCofiltered :=
    { nonempty := ⟨.mk (obj := ⊤) ⟨⟨by simp⟩⟩⟩
      cone_objs U V := by
        induction U with | @mk U hU
        induction V with | @mk V hV
        obtain ⟨⟨hU⟩⟩ := hU
        obtain ⟨⟨hV⟩⟩ := hV
        exact ⟨.mk (obj := U ⊓ V) ⟨⟨hU, hV⟩⟩,
          Functor.Elements.homMk (homOfLE (by simp)) rfl,
          Functor.Elements.homMk (homOfLE (by simp)) rfl, by tauto⟩
      cone_maps _ _ _ _ := ⟨_, 𝟙 _, rfl⟩ }
  initiallySmall := initiallySmall_of_essentiallySmall _
  jointly_surjective := by
    rintro U T hT ⟨⟨hU⟩⟩
    obtain ⟨V, f, hf, hV⟩ := hT x hU
    exact ⟨_, _, hf, ⟨⟨hV⟩⟩, rfl⟩

def points (X : Type u) [TopologicalSpace X] :
    ObjectProperty (Point.{u + 1} (Opens.grothendieckTopology X)) :=
  ObjectProperty.ofObj (point (X := X))

theorem conservative : (points X).IsConservativeFamilyOfPoints :=
  .mk' (fun U T hT x hx => by
    obtain ⟨V, f, hf, ⟨⟨hV⟩⟩, _⟩ := hT ⟨_, ⟨x⟩⟩ ⟨⟨hx⟩⟩
    exact ⟨V, f, hf, hV⟩)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.LargeZariski.Points.LargeZariskiPoints

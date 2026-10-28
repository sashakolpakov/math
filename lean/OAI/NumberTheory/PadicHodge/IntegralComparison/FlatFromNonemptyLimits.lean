import Mathlib

/-! # Flat From Nonempty Limits -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FlatFromNonemptyLimits

noncomputable section

/-!
# IntegralComparison: flatness from products, equalizers, and nonempty incoming maps

This criterion does not require a terminal object in the source site.
It applies to crystalline sites whose nilpotence level has no fixed bound.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v u' v'

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
variable (F : C ⥤ D) [HasBinaryProducts C] [HasEqualizers C]
variable [PreservesLimitsOfShape (Discrete WalkingPair) F]
variable [PreservesLimitsOfShape WalkingParallelPair F]

lemma cofilteredOrEmpty (X : D) : IsCofilteredOrEmpty (StructuredArrow X F) where
  cone_objs U V := ⟨prod U V, prod.fst, prod.snd, trivial⟩
  cone_maps {_ _} f g := ⟨equalizer f g, equalizer.ι f g, equalizer.condition f g⟩

lemma flat (h : ∀ X : D, Nonempty (StructuredArrow X F)) : RepresentablyFlat F where
  cofiltered X :=
    { cofilteredOrEmpty F X with
      nonempty := h X }

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FlatFromNonemptyLimits

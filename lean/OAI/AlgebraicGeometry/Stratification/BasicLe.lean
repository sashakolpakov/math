/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
This file has been modified.
-/
import OAI.AlgebraicGeometry.Stratification.Basic
import OAI.AlgebraicGeometry.Smooth.Locus
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-! # Basic Le -/

namespace OAI.AlgebraicGeometry.Stratification.BasicLe

noncomputable section

open _root_.AlgebraicGeometry

/-!
# A finite smooth decomposition of reduced closed subschemes

-/

/-! ### Constructions used only in proofs -/

section
open _root_.CategoryTheory _root_.Topology _root_.TopologicalSpace
universe u
variable {X : Scheme.{u}}

@[simp] lemma range_reducedClosedSubschemeι (S : Closeds X) :
    Set.range (Basic.reducedClosedSubschemeι S) = (S : Set X) :=
  Scheme.IdealSheafData.range_subschemeι _

end

section

open _root_.CategoryTheory _root_.Topology _root_.TopologicalSpace

universe u

variable {X : Scheme.{u}}

variable {K : Type u} [Field K]
  (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]

lemma reducedClosedSingularRemainder_le (S : Closeds X) :
    Basic.reducedClosedSingularRemainder f S ≤ S := by
  rintro _ ⟨x, _, rfl⟩
  exact (range_reducedClosedSubschemeι S).le ⟨x, rfl⟩

lemma reducedClosedSingularRemainder_lt [PerfectField K] (S : Closeds X) (hS : S ≠ ⊥) :
    Basic.reducedClosedSingularRemainder f S < S := by
  refine lt_of_le_of_ne (reducedClosedSingularRemainder_le f S) ?_
  have hne : Nonempty (Basic.reducedClosedSubscheme S) := by
    obtain ⟨x, hx⟩ := Closeds.coe_nonempty.mpr hS
    obtain ⟨y, _⟩ := (range_reducedClosedSubschemeι S).ge hx
    exact ⟨y⟩
  obtain ⟨x, hx⟩ :=
    (Basic.reducedClosedStructureMap f S).dense_smoothLocus_of_perfectField.nonempty
  intro h
  have hmem : Basic.reducedClosedSubschemeι S x ∈ Basic.reducedClosedSingularRemainder f S := by
    rw [h]
    exact (range_reducedClosedSubschemeι S).le ⟨x, rfl⟩
  obtain ⟨y, hy, hxy⟩ := hmem
  exact hy ((Basic.reducedClosedSubschemeι S).isClosedEmbedding.injective hxy ▸ hx)

/-- The smooth piece removed from a closed subset at one step. -/
def reducedClosedSmoothPiece (S : Closeds X) : Scheme :=
  (Basic.reducedClosedStructureMap f S).smoothLocus

/-- This piece is locally closed in the original ambient scheme. -/
def reducedClosedSmoothPieceι (S : Closeds X) : reducedClosedSmoothPiece f S ⟶ X :=
  (Basic.reducedClosedStructureMap f S).smoothLocus.ι ≫ Basic.reducedClosedSubschemeι S

set_option backward.isDefEq.respectTransparency false in
instance reducedClosedSmoothPieceι_isImmersion (S : Closeds X) :
    IsImmersion (reducedClosedSmoothPieceι f S) := by
  change IsImmersion
    ((Basic.reducedClosedStructureMap f S).smoothLocus.ι ≫ Basic.reducedClosedSubschemeι S)
  infer_instance

instance reducedClosedSmoothPiece_smooth (S : Closeds X) :
    Smooth (reducedClosedSmoothPieceι f S ≫ f) := by
  change Smooth ((Basic.reducedClosedStructureMap f S).smoothLocus.ι ≫
    Basic.reducedClosedSubschemeι S ≫ f)
  exact (OAI.AlgebraicGeometry.Smooth.Locus.Scheme.Hom.smooth_restrict_smoothLocus (Basic.reducedClosedStructureMap f S))

attribute [local instance] Basic.reducedSmoothStratificationWellFoundedRelation

open scoped Classical in
/-- The finite, explicitly recursive sequence of nonempty closed remainders. The actual
smooth strata are `reducedClosedSmoothPiece f S` for the members of this list. -/
def reducedSmoothStratification [PerfectField K] [NoetherianSpace X]
    (S : Closeds X) : List (Closeds X) :=
  if S = ⊥ then []
    else S :: reducedSmoothStratification (Basic.reducedClosedSingularRemainder f S)
termination_by S
decreasing_by
  apply reducedClosedSingularRemainder_lt f S
  assumption

end

open _root_.CategoryTheory _root_.Topology _root_.TopologicalSpace

universe u

variable {X : Scheme.{u}}

variable {K : Type u} [Field K]
  (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]

lemma reducedClosedSmoothPiece_range (S : Closeds X) :
    Set.range (reducedClosedSmoothPieceι f S) =
      (S : Set X) \ (Basic.reducedClosedSingularRemainder f S : Set X) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨(range_reducedClosedSubschemeι S).le ⟨y.1, rfl⟩, ?_⟩
    rintro ⟨z, hz, he⟩
    exact hz ((Basic.reducedClosedSubschemeι S).isClosedEmbedding.injective he ▸ y.2)
  · rintro ⟨hx, hnot⟩
    obtain ⟨y, rfl⟩ := (range_reducedClosedSubschemeι S).ge hx
    have hy : y ∈ (Basic.reducedClosedStructureMap f S).smoothLocus := by
      by_contra hn
      exact hnot ⟨y, hn, rfl⟩
    exact ⟨⟨y, hy⟩, rfl⟩

end

end OAI.AlgebraicGeometry.Stratification.BasicLe

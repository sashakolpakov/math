import OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.PositiveComplexSphere
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains

/-! # Scalar Relative Boundary Naturality -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.ScalarRelativeBoundaryNaturality

noncomputable section

/-! Naturality of the original scalar relative connecting map for actual
continuous maps of pairs. -/

open _root_.CategoryTheory _root_.HomologicalComplex OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R : Type) [CommRing R]

def scalarRelativeChainSequenceMap {X Y : TopCat.{0}} (f : X ⟶ Y)
    {A : Set X} {B : Set Y} (h : Set.MapsTo f A B) :
    CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainSequence R X A ⟶ CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainSequence R Y B where
  τ₁ := (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor R).map (CycleClass.Geometric.LocalHomology.Cycles.subspaceMap f h)
  τ₂ := (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor R).map f
  τ₃ := CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap R f h
  comm₁₂ := by
    change (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor R).map (CycleClass.Geometric.LocalHomology.Cycles.subspaceMap f h) ≫
        (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor R).map (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion Y B) =
      (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor R).map (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X A) ≫
        (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor R).map f
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, CycleClass.Geometric.LocalHomology.Cycles.subspaceMap_inclusion]
  comm₂₃ := (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection_naturality R f h).symm

theorem scalarRelativeBoundary_naturality {X Y : TopCat.{0}} (f : X ⟶ Y)
    {A : Set X} {B : Set Y} (h : Set.MapsTo f A B) (n : ℕ) :
    (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainSequence_shortExact R X A).δ (n + 1) n rfl ≫
        homologyMap ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor R).map (CycleClass.Geometric.LocalHomology.Cycles.subspaceMap f h)) n =
      homologyMap (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap R f h) (n + 1) ≫
        (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainSequence_shortExact R Y B).δ (n + 1) n rfl :=
  HomologySequence.δ_naturality (scalarRelativeChainSequenceMap R f h)
    (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainSequence_shortExact R X A) (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainSequence_shortExact R Y B)
    (n + 1) n rfl

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.ScalarRelativeBoundaryNaturality

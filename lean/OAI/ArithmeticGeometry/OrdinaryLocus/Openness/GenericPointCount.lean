import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.GeometricPointCount
import Mathlib.AlgebraicGeometry.FunctionField

/-! # Generic Point Count -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.GenericPointCount.Construction

noncomputable section

/-! A finite flat family's geometric point count is bounded by its generic count. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

/-- Geometric point counts can only increase under generalization in a
finite flat family of finite presentation. -/
theorem geometricPointCard_le_of_specializes
    {S : Scheme} (T : Over S) [IsFinite T.hom] [Flat T.hom]
    [LocallyOfFinitePresentation T.hom] {x y : S} (hxy : x ⤳ y) :
    Nat.card (DefinitionsTorsion.geometricPoint S y ⟶ T) ≤ Nat.card (DefinitionsTorsion.geometricPoint S x ⟶ T) := by
  exact hxy.mem_open (GeometricPointCount.Construction.isOpen_geometricPointCard_ge T
    (Nat.card (DefinitionsTorsion.geometricPoint S y ⟶ T))) (by
      change Nat.card (DefinitionsTorsion.geometricPoint S y ⟶ T) ≤ Nat.card (DefinitionsTorsion.geometricPoint S y ⟶ T)
      exact le_rfl)

/-- In particular, every fiber count is bounded by the count at the
generic point of an irreducible base. -/
theorem geometricPointCard_le_generic
    {S : Scheme} [IrreducibleSpace S] (T : Over S)
    [IsFinite T.hom] [Flat T.hom] [LocallyOfFinitePresentation T.hom] (s : S) :
    Nat.card (DefinitionsTorsion.geometricPoint S s ⟶ T) ≤
      Nat.card (DefinitionsTorsion.geometricPoint S (genericPoint S) ⟶ T) :=
  geometricPointCard_le_of_specializes T (genericPoint_specializes s)

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.GenericPointCount.Construction

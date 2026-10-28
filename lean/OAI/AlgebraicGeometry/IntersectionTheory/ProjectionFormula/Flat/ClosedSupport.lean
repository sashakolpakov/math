import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.ImmersionSupport
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Closed Support -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Flat.ClosedSupport

noncomputable section

/-! Flatness of a closed integral family passes to its canonical
reduced support through the actual support isomorphism. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X Y B : Scheme} [IsIntegral Y] (i : Y ⟶ X) [IsClosedImmersion i]

theorem support_range : (Closed.ImmersionSupport.support i : Set X) = Set.range i :=
  i.isClosedEmbedding.isClosed_range.closure_eq

instance flat (t : X ⟶ B) [Flat (i ≫ t)] :
    Flat (CycleClass.Geometric.GenericPoint.reducedSupportι (Closed.ImmersionSupport.support i) ≫ t) := by
  apply (MorphismProperty.cancel_left_of_respectsIso @Flat
    (Closed.ImmersionSupport.supportIso i).hom
    (CycleClass.Geometric.GenericPoint.reducedSupportι (Closed.ImmersionSupport.support i) ≫ t)).mp
  rw [← Category.assoc, Closed.ImmersionSupport.supportIso_fac]
  infer_instance

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Flat.ClosedSupport

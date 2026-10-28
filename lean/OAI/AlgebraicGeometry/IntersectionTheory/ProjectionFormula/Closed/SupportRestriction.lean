import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.SupportDimension
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Open.SupportClosure

/-! # Support Restriction -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.SupportRestriction

noncomputable section

/-! An integral support contained in a closed subscheme has the
same reduced scheme in either ambient space, with commuting embeddings. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {X Y : Scheme} (j : Y ⟶ X) [IsClosedImmersion j]
  (C : IrreducibleCloseds X) (hC : (C : Set X) ⊆ Set.range j)

abbrev support : IrreducibleCloseds Y := SupportDimension.preimage j C hC

def iso : CycleClass.Geometric.GenericPoint.reducedSupportScheme (support j C hC) ≅ CycleClass.Geometric.GenericPoint.reducedSupportScheme C :=
  ImmersionSupport.supportIso (CycleClass.Geometric.GenericPoint.reducedSupportι (support j C hC) ≫ j) ≪≫
    eqToIso (congrArg CycleClass.Geometric.GenericPoint.reducedSupportScheme (SupportDimension.imageClosure j C hC))

theorem iso_fac : (iso j C hC).hom ≫ CycleClass.Geometric.GenericPoint.reducedSupportι C =
    CycleClass.Geometric.GenericPoint.reducedSupportι (support j C hC) ≫ j := by
  rw [iso, Iso.trans_hom, eqToIso.hom, Category.assoc,
    Open.SupportClosure.inclusion_congr _ C (SupportDimension.imageClosure j C hC)]
  exact ImmersionSupport.supportIso_fac (CycleClass.Geometric.GenericPoint.reducedSupportι (support j C hC) ≫ j)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.SupportRestriction

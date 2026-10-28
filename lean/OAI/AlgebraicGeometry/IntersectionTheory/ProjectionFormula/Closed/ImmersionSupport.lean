import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Graph

/-! # Immersion Support -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.ImmersionSupport

noncomputable section

/-! An integral scheme is canonically isomorphic to the reduced
support of its image under a closed immersion. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {X Z : Scheme} [IsIntegral Z] (i : Z ⟶ X) [IsClosedImmersion i]

def support : IrreducibleCloseds X := CycleClass.Geometric.StratumClosure.integralImageClosure i

omit [IsClosedImmersion i] in
theorem support_point : CycleClass.Thom.IntersectionGeometry.supportPoint (support i) = i (genericPoint Z) := by
  have h := (genericPoint_spec Z).image i.continuous
  simp only [Set.image_univ] at h
  exact ((support i).isIrreducible.isGenericPoint_genericPoint (support i).isClosed).eq h

def supportIso : Z ≅ CycleClass.Geometric.GenericPoint.reducedSupportScheme (support i) := by
  have hk : (CycleClass.Geometric.GenericPoint.reducedSupportι (support i)).ker = i.ker := by
    change (CycleClass.Geometric.GenericPoint.reducedSupportIdeal (support i)).subschemeι.ker = _
    rw [Scheme.IdealSheafData.ker_subschemeι, CycleClass.Geometric.StratumClosure.kernel_eq_reducedImageClosureIdeal i]
    rfl
  let j := IsClosedImmersion.lift (CycleClass.Geometric.GenericPoint.reducedSupportι (support i)) i hk.le
  let : IsIso j := IsClosedImmersion.isIso_lift (CycleClass.Geometric.GenericPoint.reducedSupportι (support i)) i hk
  exact asIso j

theorem supportIso_fac : (supportIso i).hom ≫ CycleClass.Geometric.GenericPoint.reducedSupportι (support i) = i :=
  IsClosedImmersion.lift_fac _ _ _

theorem retraction_eq_inv (r : X ⟶ Z) (hr : i ≫ r = 𝟙 Z) :
    CycleClass.Geometric.GenericPoint.reducedSupportι (support i) ≫ r = (supportIso i).inv := by
  apply (cancel_epi (supportIso i).hom).mp
  rw [← Category.assoc, supportIso_fac, hr, Iso.hom_inv_id]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.ImmersionSupport

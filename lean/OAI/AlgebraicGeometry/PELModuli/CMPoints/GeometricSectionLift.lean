import OAI.AlgebraicGeometry.PELModuli.CMPoints.OrdinaryFiberCount
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PointDistinct

/-! # Geometric Section Lift -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.GeometricSectionLift

noncomputable section

/-! The canonical geometric point at the image of a field-valued
section factors through that very section. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem geometricPoint_lifts_through_field_section
    {k : Type} [Field k] (X : Over (Spec (.of k)))
    (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _)
    (x : X.left) (hx : x ∈ Set.range p) :
    ∃ l : Spec (.of (AlgebraicClosure (X.left.residueField x))) ⟶ Spec (.of k),
      l ≫ p = (ArithmeticGeometry.OrdinaryLocus.Openness.DefinitionsTorsion.geometricPoint X.left x).hom := by
  let : IsClosedImmersion p := isClosedImmersion_of_comp_eq_id X.hom p hp
  let : IsReduced (ArithmeticGeometry.OrdinaryLocus.Openness.DefinitionsTorsion.geometricPoint X.left x).left :=
    inferInstanceAs (IsReduced (Spec (.of (AlgebraicClosure (X.left.residueField x)))))
  apply ArithmeticGeometry.OrdinaryLocus.Openness.PointDistinct.Construction.exists_lift_of_range_subset_closedImmersion p
    (ArithmeticGeometry.OrdinaryLocus.Openness.DefinitionsTorsion.geometricPoint X.left x).hom
  rw [ArithmeticGeometry.OrdinaryLocus.Openness.DefinitionsTorsion.Construction.geometricPoint_range]
  exact Set.singleton_subset_iff.mpr hx

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.GeometricSectionLift

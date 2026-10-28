import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.FractionRestriction
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.LocalFraction

/-! # Fraction Identity -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.FractionIdentity

noncomputable section

/-! Any valid fraction for an ambient rational function restricts to
the same fixed function on a support when its denominator stays nonzero. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.LocalFraction.Restriction

theorem eq (X : Scheme) [IsIntegral X] (W : IrreducibleCloseds X)
    (hz : CycleClass.Thom.IntersectionGeometry.supportPoint W ∈ (W : Set X)) (x : X) (hx : x ∈ (W : Set X))
    (u : X.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint W)) (hu : IsUnit u)
    (a b : X.presheaf.stalk x) (hb : Local.Principal.supportStalkMap X W x hx b ≠ 0)
    (hab : algebraMap (X.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint W)) X.functionField u =
      algebraMap (X.presheaf.stalk x) X.functionField a /
        algebraMap (X.presheaf.stalk x) X.functionField b) :
    LocalFraction.Restriction.toFunctionField X W (CycleClass.Thom.IntersectionGeometry.supportPoint W) hz u =
      LocalFraction.Restriction.toFunctionField X W x hx a / LocalFraction.Restriction.toFunctionField X W x hx b := by
  obtain ⟨c, d, _, hd, hcd, hg⟩ := LocalFraction.exists_fraction X W hz x hx u hu
  let φ := LocalFraction.Restriction.toFunctionField X W x hx
  have hbφ : φ b ≠ 0 := by
    change algebraMap ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W).presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPreimage W x hx))
      (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField (Local.Principal.supportStalkMap X W x hx b) ≠ 0
    exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hb
  have hdφ : φ d ≠ 0 := by
    change algebraMap ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W).presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPreimage W x hx))
      (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField (Local.Principal.supportStalkMap X W x hx d) ≠ 0
    exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hd
  have he := FractionRestriction.eq φ.hom a b c d hbφ hdφ (hab.symm.trans hcd)
  exact hg.trans he.symm

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.FractionIdentity

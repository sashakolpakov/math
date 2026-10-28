import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralChernVanishing
import OAI.RepresentationTheory.Theta.Geometric.ClosedFormPicardZero
import OAI.RepresentationTheory.Theta.Geometric.AbelianAntiholomorphicInvariant

/-! # Homogeneous Invariant Representative -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HomogeneousInvariantRepresentative

noncomputable section

/-! Every homogeneous algebraic line class on the native abelian variety
is represented by an actual closed, translation-invariant form of type
(0,1), through the proved holomorphic exponential map. -/

open scoped _root_.CategoryTheory.MonObj

theorem homogeneousLineBundle_closedForm_representative (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (L : HilbertConstruction.Line.Bundles.LineBundle A.toOver.left)
    (hL : HomogeneousLinePowers.IsHomogeneousLineClass (RepresentationTheory.Theta.Geometric.AbelianScheme.abelianSchemeOfVariety A) (HilbertConstruction.Line.Bundles.LineBundle.classOf L)) :
    ∃ a : RepresentationTheory.Theta.Geometric.ClosedPureDolbeaultMap.ClosedType01Forms A.variety.analyticModel A.variety.analyticSpace,
      RepresentationTheory.Theta.Geometric.ClosedFormPicardZero.closedFormPicardMap A.variety a = HolomorphicLineClass.nativeHolomorphicLineClass A.variety L :=
  RepresentationTheory.Theta.Geometric.ClosedFormPicardZero.exists_closedForm_of_zeroChern A.variety (HolomorphicLineClass.nativeHolomorphicLineClass A.variety L)
    (IntegralChernVanishing.homogeneousLineBundle_integralConnecting_eq_zero A L hL)

theorem homogeneousLineBundle_invariantForm_representative (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (L : HilbertConstruction.Line.Bundles.LineBundle A.toOver.left)
    (hL : HomogeneousLinePowers.IsHomogeneousLineClass (RepresentationTheory.Theta.Geometric.AbelianScheme.abelianSchemeOfVariety A) (HilbertConstruction.Line.Bundles.LineBundle.classOf L)) :
    ∃ a : RepresentationTheory.Theta.Geometric.ClosedPureDolbeaultMap.ClosedType01Forms A.variety.analyticModel A.variety.analyticSpace,
      RepresentationTheory.Theta.Geometric.ClosedFormPicardZero.closedFormPicardMap A.variety a = HolomorphicLineClass.nativeHolomorphicLineClass A.variety L ∧
        a.val.val ∈ AbelianVariety.InvariantClosed.Constructions.ExteriorCohomology.invariantForms
          (E := A.variety.analyticModel) (G := A.variety.analyticSpace) 1 := by
  obtain ⟨a, ha⟩ := homogeneousLineBundle_closedForm_representative A L hL
  exact ⟨a, ha, RepresentationTheory.Theta.Geometric.AbelianAntiholomorphicInvariant.abelian_closedType01_invariant A a⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HomogeneousInvariantRepresentative

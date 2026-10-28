import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntersectSupportOpenNaturality
import OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.GoodShift
import OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.SupportedRelative

/-! # Intersect Open Naturality -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.IntersectOpenNaturality.Constructions.Construction

noncomputable section

/-! The actual closed-complex-immersion Thom comparison retains the specified support. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntersectSupportOpenNaturality.Constructions
set_option backward.isDefEq.respectTransparency false

variable {V : Closed.ComplexImmersion.Constructions.ComplexManifold} {p : ℕ} (Z : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V p)

theorem regularThomClosedSupportRelativeIso_open_naturality
    (O : Opens Z.regularAmbientSpace) {U W : Opens Z.regularAmbientSpace} (i : U ⟶ W) (n : ℕ) :
    HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex
          (HodgeConjecture.DegreeTwo.SupportSectionChanges.Constructions.closedSupportSectionRestriction (R := ℚ) (X := TopCat.of Z.regularAmbientSpace) O i)
          (ComplexShape.up ℕ)).app (GoodShift.Constructions.Construction.regularThomGoodShiftSheafComplex Z)) n ≫
        (SupportedRelative.Constructions.Construction.regularThomClosedSupportRelativeIso Z O U n).hom =
      (SupportedRelative.Constructions.Construction.regularThomClosedSupportRelativeIso Z O W n).hom ≫
        HomologicalComplex.homologyMap
          ((AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCochainPresheaf (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace)
            ((Z.regularThomComplementOpen ⊔ O : Opens Z.regularAmbientSpace) : Set Z.regularAmbientSpace)).map i.op)
          (2*p+n) := by
  simp only [SupportedRelative.Constructions.Construction.regularThomClosedSupportRelativeIso, Iso.trans_hom]
  rw [← Category.assoc, HodgeConjecture.DegreeTwo.ClosedSupportShiftNaturality.Constructions.closedSupportGoodShiftCohomologyIso_naturality,
    Category.assoc, HodgeConjecture.DegreeTwo.IntersectSupportOpenNaturality.Constructions.intersectSupportedRelativeCohomologyIso_open_naturality,
    ← Category.assoc]

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.IntersectOpenNaturality.Constructions.Construction

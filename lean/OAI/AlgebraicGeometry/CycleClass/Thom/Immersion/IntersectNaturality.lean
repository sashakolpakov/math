import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntersectSupportNaturality
import OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.GoodShift
import OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.SupportedRelative

/-! # Intersect Naturality -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.IntersectNaturality.Constructions.Construction

noncomputable section

/-! The actual closed-complex-immersion Thom comparison retains the specified support. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntersectSupportNaturality.Constructions
set_option backward.isDefEq.respectTransparency false

variable {V : Closed.ComplexImmersion.Constructions.ComplexManifold} {p : ℕ} (Z : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V p)

theorem regularThomClosedSupportRelativeIso_support_naturality
    {O P : Opens Z.regularAmbientSpace} (h : O ≤ P) (U : Opens Z.regularAmbientSpace) (n : ℕ) :
    HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex
          (HodgeConjecture.DegreeTwo.SupportSectionChanges.Constructions.closedSupportSectionChange (R := ℚ) (X := TopCat.of Z.regularAmbientSpace) h U)
          (ComplexShape.up ℕ)).app (GoodShift.Constructions.Construction.regularThomGoodShiftSheafComplex Z)) n ≫
        (SupportedRelative.Constructions.Construction.regularThomClosedSupportRelativeIso Z O U n).hom =
      (SupportedRelative.Constructions.Construction.regularThomClosedSupportRelativeIso Z P U n).hom ≫
        HomologicalComplex.homologyMap
          (HodgeConjecture.DegreeTwo.IntersectSupportNaturality.Constructions.relativeOpenComplementChange (X := TopCat.of Z.regularAmbientSpace)
            (sup_le_sup_left h Z.regularThomComplementOpen) U) (2*p+n) := by
  simp only [SupportedRelative.Constructions.Construction.regularThomClosedSupportRelativeIso, Iso.trans_hom]
  rw [← Category.assoc, HodgeConjecture.DegreeTwo.ClosedSupportShiftNaturality.Constructions.closedSupportGoodShiftCohomologyIso_naturality,
    Category.assoc, HodgeConjecture.DegreeTwo.IntersectSupportNaturality.Constructions.intersectSupportedRelativeCohomologyIso_support_naturality,
    ← Category.assoc]

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.IntersectNaturality.Constructions.Construction

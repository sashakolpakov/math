import OAI.AlgebraicGeometry.DivisorClass.Chern.ClosedSupportFunctor
import OAI.AlgebraicGeometry.DivisorClass.Chern.FlasqueSupportedComparison
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.FlasqueDerivedComparison

/-! # Derived Comparison -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Supported.DerivedComparison

noncomputable section

/-! The actual complex of sections with closed support computes the native derived supported-section functor. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.FlasqueDerivedComparison.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}} (O U : Opens X)

def supportedSectionsFunctor : TopCat.Sheaf (ModuleCat.{0} ℚ) X ⥤ ModuleCat.{0} ℚ :=
  ClosedSupportFunctor.closedSupportSheafFunctor O ⋙ CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U

instance supportedSectionsFunctor_additive : (supportedSectionsFunctor O U).Additive :=
  inferInstanceAs ((ClosedSupportFunctor.closedSupportSheafFunctor O ⋙ CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (R := ℚ) U).Additive)

def supportedSectionsFunctorIso
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ℕ) :
    CycleClass.Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsComplex U (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplex O K) ≅
      ((supportedSectionsFunctor O U).mapHomologicalComplex (ComplexShape.up ℕ)).obj K :=
  ((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).mapHomologicalComplex (ComplexShape.up ℕ)).mapIso
    (ClosedSupportFunctor.supportedSheafComplexFunctorIso O K)

theorem supportedSectionsFunctorIso_naturality
    {K L : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ℕ} (f : K ⟶ L) :
    ((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (R := ℚ) U).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (SectionQuasiIso.supportedSheafComplexMap O f) ≫ (supportedSectionsFunctorIso O U L).hom =
      (supportedSectionsFunctorIso O U K).hom ≫
        ((supportedSectionsFunctor O U).mapHomologicalComplex (ComplexShape.up ℕ)).map f := by
  have h := congrArg
    (((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (R := ℚ) U).mapHomologicalComplex (ComplexShape.up ℕ)).map)
    (ClosedSupportFunctor.supportedSheafComplexFunctorIso_naturality O f)
  rw [Functor.map_comp, Functor.map_comp] at h
  exact h

variable (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ℕ)
variable (hK : ∀ n, TopCat.Sheaf.IsFlasque (K.X n)) (he : ∀ n, K.ExactAt (n+1))

def flasqueSupportedDerivedCohomologyIso (n : ℕ) :
    (CycleClass.Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsComplex U (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplex O K)).homology n ≅
      ((supportedSectionsFunctor O U).rightDerived n).obj (K.homology 0) :=
  FlasqueSupportedComparison.flasqueSupportedResolutionCohomologyIso O K hK he
      (HodgeConjecture.DegreeTwo.FlasqueDerivedComparison.Constructions.rationalSheafInjectiveResolution (K.homology 0)) U n ≪≫
    (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) n).mapIso
      (supportedSectionsFunctorIso O U (HodgeConjecture.DegreeTwo.FlasqueDerivedComparison.Constructions.rationalSheafInjectiveResolution (K.homology 0)).cocomplex) ≪≫
    ((HodgeConjecture.DegreeTwo.FlasqueDerivedComparison.Constructions.rationalSheafInjectiveResolution (K.homology 0)).isoRightDerivedObj
      (supportedSectionsFunctor O U) n).symm

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Supported.DerivedComparison

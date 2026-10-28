import OAI.AlgebraicGeometry.Crystalline.Cohomology.ZariskiOpenModules
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CoefficientResolution
import OAI.AlgebraicGeometry.Crystalline.Cohomology.ExactInjective
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.Cover

/-! # Restricted Coefficient -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.RestrictedCoefficient.RestrictedCoefficientResolution

noncomputable section

/-! # Exact sections of the original injective resolution after restriction to an acyclic open -/

open _root_.CategoryTheory _root_.CategoryTheory.Abelian _root_.AlgebraicGeometry

universe u

variable (R : Type u) [CommRing R] {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]

local instance restrictionInjectives :
    (Cech.Cover.CechRestriction.sheafRestrictionFunctor R f).PreservesInjectiveObjects :=
  ZariskiOpenModules.ZariskiOpenInjectives.restriction_preservesInjectives R f

local instance coefficientExt : HasExt.{u + 1}
    (Sheaf (Opens.grothendieckTopology Y) (ModuleCat.{u} R)) := HasExt.standard _

theorem exactAt {F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)}
    (I : InjectiveResolution F) (n : ℕ)
    [Subsingleton (Ext.{u + 1} (ConstantSheaf.ConstantSheafSections.coefficient R (TopCat.of Y))
      ((Cech.Cover.CechRestriction.sheafRestrictionFunctor R f).obj F) (n + 1))] :
    ((((Cech.Cover.CechRestriction.sheafRestrictionFunctor R f) ⋙
      CoefficientResolution.CoefficientResolutionExactness.sections R (TopCat.of Y)).mapHomologicalComplex (.up ℕ)).obj
        I.cocomplex).ExactAt (n + 1) :=
  CoefficientResolution.CoefficientResolutionExactness.exactAt R (TopCat.of Y)
    (ExactInjective.ExactInjectiveResolution.map (Cech.Cover.CechRestriction.sheafRestrictionFunctor R f) I) n

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.RestrictedCoefficient.RestrictedCoefficientResolution

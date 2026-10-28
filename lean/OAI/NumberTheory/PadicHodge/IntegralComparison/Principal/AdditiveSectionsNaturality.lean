import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.AdditiveSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.CoefficientNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.ExactHomology

/-! # Additive Sections Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.AdditiveSectionsNaturality

noncomputable section

/-! Forgetting the affine scalar ring is natural for the original
principal supported cohomology, including the negative-resolution maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u
variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)
  {K L : CochainComplex X.Modules ℕ} (a : K ⟶ L)

def linearMap : AdditiveSections.linearComplex U hU K ⟶ AdditiveSections.linearComplex U hU L :=
  ((ModuleFunctor.functor U hU).mapHomologicalComplex (.up ℕ)).map a

def additiveMap : AdditiveSections.additiveComplex U hU K ⟶ AdditiveSections.additiveComplex U hU L :=
  ((AdditiveSections.additiveFunctor U hU).mapHomologicalComplex (.up ℕ)).map a

theorem complexIso_naturality :
    AugmentedCech.CoefficientNaturality.Total.mappedComplexMap (AdditiveSections.forgetScalars U) (linearMap U hU a) ≫
      (AdditiveSections.complexIso U hU L).hom = (AdditiveSections.complexIso U hU K).hom ≫ additiveMap U hU a :=
  (NatIso.mapHomologicalComplex (AdditiveSections.functorIso U hU) (.up ℕ)).hom.naturality a

variable {ι : Type u} [LinearOrder ι] (W : ι → SectionPresheaf.Index U)

local instance naturalityFiniteBiproducts : HasFiniteBiproducts (ModuleCat.{u} Γ(X, U)) :=
  Abelian.hasFiniteBiproducts

def linearTotalMap := AugmentedCech.CoefficientNaturality.Total.totalMap W (linearMap U hU a)
def additiveTotalMap := AugmentedCech.CoefficientNaturality.Total.totalMap W (additiveMap U hU a)

theorem totalIso_naturality :
    ((AdditiveSections.forgetScalars U).mapHomologicalComplex (.up ℕ)).map (linearTotalMap U hU a W) ≫
      (AdditiveSections.totalIso U hU L W).hom =
        (AdditiveSections.totalIso U hU K W).hom ≫ additiveTotalMap U hU a W := by
  let F := (AugmentedOrdered.CechFunctor.functor W (D := AddCommGrpCat.{u})).mapHomologicalComplex
    (.up ℕ) ⋙ HomologicalComplex₂.totalFunctor AddCommGrpCat.{u} (.up ℕ) (.up ℕ) (.up ℕ)
  have hc := AugmentedCech.CoefficientNaturality.Total.totalIso_naturality W (AdditiveSections.forgetScalars U)
    (linearMap U hU a)
  have ht := congrArg F.map (complexIso_naturality U hU a)
  simp only [Functor.map_comp] at ht
  change ((AdditiveSections.forgetScalars U).mapHomologicalComplex (.up ℕ)).map (linearTotalMap U hU a W) ≫
      ((AugmentedCech.CoefficientTotal.totalIso W (AdditiveSections.forgetScalars U) (AdditiveSections.linearComplex U hU L)).hom ≫
        F.map (AdditiveSections.complexIso U hU L).hom) =
    ((AugmentedCech.CoefficientTotal.totalIso W (AdditiveSections.forgetScalars U) (AdditiveSections.linearComplex U hU K)).hom ≫
      F.map (AdditiveSections.complexIso U hU K).hom) ≫ F.map (additiveMap U hU a)
  simp only [linearTotalMap]
  erw [← Category.assoc, hc, Category.assoc, ht, Category.assoc]

theorem homologyIso_naturality (q : ℕ) :
    (AdditiveSections.forgetScalars U).map (homologyMap (linearTotalMap U hU a W) q) ≫
      (AdditiveSections.homologyIso U hU L W q).hom =
        (AdditiveSections.homologyIso U hU K W q).hom ≫ homologyMap (additiveTotalMap U hU a W) q :=
  GeometricComparison.ExactHomology.ExactHomologyComparison.naturality (AdditiveSections.forgetScalars U) (.up ℕ)
    (AdditiveSections.totalIso U hU K W) (AdditiveSections.totalIso U hU L W)
    (linearTotalMap U hU a W) (additiveTotalMap U hU a W)
    (totalIso_naturality U hU a W) q

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.AdditiveSectionsNaturality

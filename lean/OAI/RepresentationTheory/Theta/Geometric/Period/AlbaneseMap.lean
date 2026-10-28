import OAI.RepresentationTheory.Theta.Geometric.ComponentAlbaneseBetti
import OAI.RepresentationTheory.Theta.Geometric.Geometry
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ComplexAlbaneseCoordinates

/-! # Albanese Map -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The period component's actual Albanese map and its H¹ isomorphism,
with the single and iterated base changes compared explicitly. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

def Data.ActiveHeckeThetaData.periodComponentComparison (j : Fin D.pel.componentCount) :
    D.pel.components.complexSurface D.pel.complexPoint j ≅ D.componentComplex j :=
  (Over.pullbackComp D.pel.complexGenericPoint D.pel.generic).app (D.pel.components.S j)

def Data.ActiveHeckeThetaData.periodComponentAlbaneseMap (hg : D.pel.HasIntegralModelGeometry)
    (j : Fin D.pel.componentCount) (X : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (component : X.toOver ≅ D.componentComplex j) :
    X.toOver ⟶ (D.pel.actualComplexComponentAlbaneseVariety hg j).toOver :=
  component.hom ≫ (D.periodComponentComparison j).inv ≫
    D.pel.components.complexMap D.pel.complexPoint j

theorem Data.ActiveHeckeThetaData.periodComponentAlbaneseMap_betti_bijective (hg : D.pel.HasIntegralModelGeometry)
    (j : Fin D.pel.componentCount) (X : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (component : X.toOver ≅ D.componentComplex j) :
    Function.Bijective (AlgebraicGeometry.Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) 1
      (D.periodComponentAlbaneseMap hg j X component)) := by
  change Function.Bijective (AlgebraicGeometry.PELModuli.IntegralModel.Product.bettiPullbackQ
    (component.hom ≫ (D.periodComponentComparison j).inv ≫
      D.pel.components.complexMap D.pel.complexPoint j) 1)
  rw [AlgebraicGeometry.PELModuli.IntegralModel.Product.bettiPullbackQ_comp, AlgebraicGeometry.PELModuli.IntegralModel.Product.bettiPullbackQ_comp]
  exact (AlgebraicGeometry.PELModuli.IntegralModel.ProductDimensions.bettiIso component 1).bijective.comp
    ((AlgebraicGeometry.PELModuli.IntegralModel.ProductDimensions.bettiIso (D.periodComponentComparison j).symm 1).bijective.comp
      (ComponentAlbaneseBetti.SphericalPELAlbaneseData.complexComponentAlbanese_betti_bijective D.pel hg j))

theorem Data.ActiveHeckeThetaData.componentAlbanese_coordinate_self (hg : D.pel.HasIntegralModelGeometry)
    (j : Fin D.pel.componentCount) :
    D.componentComplexInclusion j ≫ D.pel.complexAlbaneseMap hg ≫
      D.pel.complexAlbaneseProjection j =
    (D.periodComponentComparison j).inv ≫ D.pel.components.complexMap D.pel.complexPoint j := by
  have h := congrArg ((D.periodComponentComparison j).inv ≫ ·)
    (D.pel.complexAlbanese_component_self hg j)
  change (D.periodComponentComparison j).inv ≫
    ((D.periodComponentComparison j).hom ≫ D.componentComplexInclusion j) ≫
      D.pel.complexAlbaneseMap hg ≫ D.pel.complexAlbaneseProjection j = _ at h
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using h

theorem Data.ActiveHeckeThetaData.componentAlbanese_coordinate_ne (hg : D.pel.HasIntegralModelGeometry)
    (i j : Fin D.pel.componentCount) (hij : i ≠ j) :
    D.componentComplexInclusion i ≫ D.pel.complexAlbaneseMap hg ≫
      D.pel.complexAlbaneseProjection j = 1 := by
  have h := congrArg ((D.periodComponentComparison i).inv ≫ ·)
    (D.pel.complexAlbanese_component_ne hg i j hij)
  change (D.periodComponentComparison i).inv ≫
    ((D.periodComponentComparison i).hom ≫ D.componentComplexInclusion i) ≫
      D.pel.complexAlbaneseMap hg ≫ D.pel.complexAlbaneseProjection j = _ at h
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, CategoryTheory.MonObj.comp_one] using h

end

end OAI.RepresentationTheory.Theta.Geometric

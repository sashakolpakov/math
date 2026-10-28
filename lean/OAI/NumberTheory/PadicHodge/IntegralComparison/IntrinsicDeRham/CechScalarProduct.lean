import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.ScalarProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.CechCoefficient.MorphismCohomologyCup
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.BaseChangeTotalCup
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicCechScalarBicomplex

/-! # Cech Scalar Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.CechScalarProduct.Intrinsic

noncomputable section

/-! Actual scalar extension and geometric pullback preserve the cup
product on the original finite ordinary de Rham Čech total. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
  (X : Over (Spec (CommRingCat.of R))) (Y : Over (Spec (CommRingCat.of S)))
  (f : Y.left ⟶ X.left)
  (h : f ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)))
  {ι : Type} [Finite ι] (U : ι → X.left.Opens)

local instance : PreservesFiniteLimits (TopologicalSpace.Opens.map f.base) :=
  AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicCechScalarBicomplex.BaseIntrinsicCechScalarBicomplex.opensFiniteLimits R S X Y f

abbrev coefficientMap := CechCoefficient.MorphismTotalCup.cochainMap
  (GeometricComparison.FlatScalar.FlatScalarExtension.moduleFunctor R S) (NonemptyCechNerve.nerve U)
  (AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicCechScalarBicomplex.BaseIntrinsicCechScalarBicomplex.finiteIndices R X U) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X)
  (((AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicPresheafScalarComplex.BaseIntrinsicPresheafScalarComplex.preimage R S X Y f).mapHomologicalComplex (.up ℕ)).obj
    (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex S Y))
  (AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicPresheafScalarComplex.BaseIntrinsicPresheafScalarComplex.map R S X Y f h)

abbrev coverMap := Cech.BaseChangeTotalCup.Product.map
  (TopologicalSpace.Opens.map f.base) U (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex S Y)

def cochainMap :
    ((GeometricComparison.FlatScalar.FlatScalarExtension.moduleFunctor R S).mapHomologicalComplex (.up ℕ)).obj
      (IntegralDeRham.CechProduct.total R X (NonemptyCechNerve.nerve U)) ⟶
    IntegralDeRham.CechProduct.total S Y (NonemptyCechNerve.nerve (fun i => f ⁻¹ᵁ U i)) :=
  coefficientMap R S X Y f h U ≫ coverMap R S X Y f U

def map (n : ℕ) :
    (IntegralDeRham.CechProduct.total R X (NonemptyCechNerve.nerve U)).X n →+
    (IntegralDeRham.CechProduct.total S Y (NonemptyCechNerve.nerve (fun i => f ⁻¹ᵁ U i))).X n :=
  ((cochainMap R S X Y f h U).f n).hom.toAddMonoidHom.comp
    (ScalarProduct.Intrinsic.unit R S _)

theorem map_cup (n m : ℕ)
    (x : (IntegralDeRham.CechProduct.total R X (NonemptyCechNerve.nerve U)).X n)
    (y : (IntegralDeRham.CechProduct.total R X (NonemptyCechNerve.nerve U)).X m) :
    Intrinsic.map R S X Y f h U (n+m)
      (IntegralDeRham.CechProduct.totalCup R X (NonemptyCechNerve.nerve U) n m x y) =
    IntegralDeRham.CechProduct.totalCup S Y
      (NonemptyCechNerve.nerve (fun i => f ⁻¹ᵁ U i)) n m
      (Intrinsic.map R S X Y f h U n x) (Intrinsic.map R S X Y f h U m y) := by
  have hc := CechCoefficient.MorphismTotalCup.map_cup
    (GeometricComparison.FlatScalar.FlatScalarExtension.moduleFunctor R S) (ScalarProduct.Intrinsic.unit R S)
    (ScalarProduct.Intrinsic.unit_natural R S)
    (NonemptyCechNerve.nerve U) (AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicCechScalarBicomplex.BaseIntrinsicCechScalarBicomplex.finiteIndices R X U)
    (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X)
    (((AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicPresheafScalarComplex.BaseIntrinsicPresheafScalarComplex.preimage R S X Y f).mapHomologicalComplex (.up ℕ)).obj
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex S Y))
    (AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicPresheafScalarComplex.BaseIntrinsicPresheafScalarComplex.map R S X Y f h)
    (IntegralDeRham.CechProduct.sectionPairing R X)
    (ScalarProduct.Intrinsic.targetPairing R S X Y f)
    (ScalarProduct.Intrinsic.component_product R S X Y f h) n m x y
  exact (congrArg ((coverMap R S X Y f U).f (n+m)) hc).trans
    (Cech.BaseChangeTotalCup.Product.map_cup (TopologicalSpace.Opens.map f.base) U
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex S Y) (IntegralDeRham.CechProduct.sectionPairing S Y)
      (IntegralDeRham.CechProduct.sectionPairing_natural S Y) n m _ _)

variable [Module.Flat R S]

abbrev homologyMap := CoefficientCochainCup.map (GeometricComparison.FlatScalar.FlatScalarExtension.moduleFunctor R S)
  (ScalarProduct.Intrinsic.unit R S)
  (IntegralDeRham.CechProduct.total R X (NonemptyCechNerve.nerve U))
  (IntegralDeRham.CechProduct.total S Y (NonemptyCechNerve.nerve (fun i => f ⁻¹ᵁ U i)))
  (cochainMap R S X Y f h U)

abbrev homologyMap_cup := CoefficientCochainCup.map_cup
  (GeometricComparison.FlatScalar.FlatScalarExtension.moduleFunctor R S) (ScalarProduct.Intrinsic.unit R S)
  (ScalarProduct.Intrinsic.unit_natural R S)
  (IntegralDeRham.CechProduct.total R X (NonemptyCechNerve.nerve U))
  (IntegralDeRham.CechProduct.total S Y (NonemptyCechNerve.nerve (fun i => f ⁻¹ᵁ U i)))
  (cochainMap R S X Y f h U)
  (IntegralDeRham.CechProduct.totalCup R X (NonemptyCechNerve.nerve U))
  (IntegralDeRham.CechProduct.totalCup S Y (NonemptyCechNerve.nerve (fun i => f ⁻¹ᵁ U i)))
  (Presheaf.TotalLeibniz.CechProduct.differential_totalCup (NonemptyCechNerve.nerve U)
    (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X) (IntegralDeRham.CechProduct.sectionPairing R X)
    (IntegralDeRham.CechProduct.sectionPairing_natural R X)
    (IntegralDeRham.CechProduct.sectionPairing_differential R X))
  (Presheaf.TotalLeibniz.CechProduct.differential_totalCup (NonemptyCechNerve.nerve (fun i => f ⁻¹ᵁ U i))
    (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex S Y) (IntegralDeRham.CechProduct.sectionPairing S Y)
    (IntegralDeRham.CechProduct.sectionPairing_natural S Y)
    (IntegralDeRham.CechProduct.sectionPairing_differential S Y))
  (map_cup R S X Y f h U)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.CechScalarProduct.Intrinsic

import OAI.NumberTheory.PadicHodge.IntegralComparison.BaseCechTotalForget
import OAI.NumberTheory.PadicHodge.IntegralComparison.CechCoefficient.Total
import OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.DeRhamSheafIso
import Mathlib.Algebra.Category.ModuleCat.AB

/-! # De Rham Cech Total -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.DeRhamCechTotal

noncomputable section

/-! The original de Rham sheaf Čech total and its canonical Frobenius module comparison. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

universe u

variable (k : Type u) [Field k] [Fintype k]
  (X : Over (Spec (CommRingCat.of k)))

def presheaves : Sheaf (Opens.grothendieckTopology X.left) (ModuleCat.{u} k) ⥤
    X.left.Opensᵒᵖ ⥤ ModuleCat.{u} k :=
  sheafToPresheaf (Opens.grothendieckTopology X.left) (ModuleCat.{u} k)

instance presheaves_additive : (presheaves k X).Additive where
  map_add := rfl

def presheafComplex : CochainComplex (X.left.Opensᵒᵖ ⥤ ModuleCat.{u} k) ℕ :=
  ((presheaves k X).mapHomologicalComplex (.up ℕ)).obj (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex k X)

def abPresheaves : Sheaf (Opens.grothendieckTopology X.left) (ModuleCat.{u} k) ⥤
    X.left.Opensᵒᵖ ⥤ AddCommGrpCat.{u} :=
  presheaves k X ⋙ (Functor.whiskeringRight _ _ _).obj (forget₂ (ModuleCat.{u} k) AddCommGrpCat.{u})

instance abPresheaves_additive : (abPresheaves k X).Additive where
  map_add := rfl

def abComplex : CochainComplex (X.left.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) ℕ :=
  CechCoefficient.Total.mappedComplex (forget₂ (ModuleCat.{u} k) AddCommGrpCat.{u}) (presheafComplex k X)

def underlyingIso :
    ((BaseCechTotalForget.presheaves (X := X.left)).mapHomologicalComplex (.up ℕ)).obj
      (Frobenius.DeRhamGlobal.complex k X) ≅ abComplex k X :=
  ((abPresheaves k X).mapHomologicalComplex (.up ℕ)).mapIso (Frobenius.DeRhamSheafIso.iso k X)

variable {ι : Type u} (U : ι → X.left.Opens)

def bicomplex : HomologicalComplex₂ (ModuleCat.{u} k) (.up ℕ) (.up ℕ) :=
  CechCoefficient.Total.bicomplex (FormalCoproduct.mk ι U).cech (presheafComplex k X)

def total : CochainComplex (ModuleCat.{u} k) ℕ := (bicomplex k X U).total (.up ℕ)

def abBicomplex : HomologicalComplex₂ AddCommGrpCat.{u} (.up ℕ) (.up ℕ) :=
  CechCoefficient.Total.bicomplex (FormalCoproduct.mk ι U).cech (abComplex k X)

def abTotal : CochainComplex AddCommGrpCat.{u} ℕ := (abBicomplex k X U).total (.up ℕ)

def forgetTotalIso :
    ((forget₂ (ModuleCat.{u} k) AddCommGrpCat.{u}).mapHomologicalComplex (.up ℕ)).obj (DeRhamCechTotal.total k X U) ≅
      abTotal k X U :=
  CechCoefficient.Total.totalIso (forget₂ (ModuleCat.{u} k) AddCommGrpCat.{u})
    (FormalCoproduct.mk ι U).cech (presheafComplex k X)

def frobeniusBicomplexIso :
    BaseCechTotalForget.abBicomplex U (Frobenius.DeRhamGlobal.complex k X) ≅ abBicomplex k X U :=
  ((FormalCoproduct.cochainComplexFunctor (FormalCoproduct.mk ι U).cech).mapHomologicalComplex (.up ℕ)).mapIso
    (underlyingIso k X)

def frobeniusTotalIso :
    ((AlgebraicGeometry.SheafCohomology.Projective.BaseCechForget.Scheme.Modules.baseModuleForget (Spec (CommRingCat.of k))).mapHomologicalComplex (.up ℕ)).obj
      ((BaseCechTotalForget.baseBicomplex X.hom U
        (Frobenius.DeRhamGlobal.complex k X)).total (.up ℕ)) ≅ abTotal k X U :=
  BaseCechTotalForget.totalIso X.hom U (Frobenius.DeRhamGlobal.complex k X) ≪≫
    HomologicalComplex₂.total.mapIso (frobeniusBicomplexIso k X U) (.up ℕ)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.DeRhamCechTotal

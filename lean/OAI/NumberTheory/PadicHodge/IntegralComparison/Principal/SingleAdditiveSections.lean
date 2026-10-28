import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.AdditiveSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCechForgetHomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.Closed.SupportedSurvivor

/-! # Single Additive Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SingleAdditiveSections

noncomputable section

/-! The scalar-forgotten principal diagram of a single survivor is
the original additive survivor sheaf used by global supported extension. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.AdditiveSections
variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)

def sheafComplex (K : CochainComplex X.Modules ℕ) :=
  ((SheafOfModules.toSheaf X.ringCatSheaf).mapHomologicalComplex (.up ℕ)).obj K

def diagramIso (K : CochainComplex X.Modules ℕ) : AdditiveSections.additiveComplex U hU K ≅
    SupportedOrderedCechEdge.Abelian.presheafComplex AddCommGrpCat.{u} X (AdditiveSections.opens U hU)
      (sheafComplex K) := Iso.refl _

variable (S : X.Modules) (c : ℕ)

abbrev moduleSingle := (single X.Modules (.up ℕ) c).obj S
abbrev sheafSingle := Closed.SupportedSurvivor.single S c
abbrev sheafDiagram := SupportedOrderedCechEdge.Abelian.presheafComplex
  AddCommGrpCat.{u} X (AdditiveSections.opens U hU) (sheafSingle S c)

def singleIso : AdditiveSections.additiveComplex U hU (moduleSingle S c) ≅ sheafDiagram U hU S c :=
  diagramIso U hU (moduleSingle S c) ≪≫
    ((SupportedOrderedCechEdge.Abelian.presheaves AddCommGrpCat.{u} X
      (AdditiveSections.opens U hU)).mapHomologicalComplex (.up ℕ)).mapIso
        ((HomologicalComplex.singleMapHomologicalComplex (SheafOfModules.toSheaf X.ringCatSheaf)
          (.up ℕ) c).app S)

variable {ι : Type u} [LinearOrder ι] (W : ι → SectionPresheaf.Index U)

def totalIso : ((AdditiveSections.forgetScalars U).mapHomologicalComplex (.up ℕ)).obj
    ((AugmentedOrdered.CechFunctor.bicomplex W (AdditiveSections.linearComplex U hU (moduleSingle S c))).total (.up ℕ)) ≅
      (AugmentedOrdered.CechFunctor.bicomplex W (sheafDiagram U hU S c)).total (.up ℕ) :=
  AdditiveSections.totalIso U hU (moduleSingle S c) W ≪≫
    HomologicalComplex₂.total.mapIso
      (((AugmentedOrdered.CechFunctor.functor W).mapHomologicalComplex (.up ℕ)).mapIso
        (singleIso U hU S c)) (.up ℕ)

def homologyIso (q : ℕ) : (AdditiveSections.forgetScalars U).obj
    (((AugmentedOrdered.CechFunctor.bicomplex W (AdditiveSections.linearComplex U hU (moduleSingle S c))).total
      (.up ℕ)).homology q) ≅
        ((AugmentedOrdered.CechFunctor.bicomplex W (sheafDiagram U hU S c)).total (.up ℕ)).homology q :=
  AdditiveSections.homologyIso U hU (moduleSingle S c) W q ≪≫
    homologyMapIso (HomologicalComplex₂.total.mapIso
      (((AugmentedOrdered.CechFunctor.functor W).mapHomologicalComplex (.up ℕ)).mapIso
        (singleIso U hU S c)) (.up ℕ)) q

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SingleAdditiveSections

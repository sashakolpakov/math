import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ModuleFunctor
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.CoefficientTotal
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-! # Additive Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.AdditiveSections

noncomputable section

/-! Forgetting the affine scalar ring gives exactly the original
additive sheaf sections on every principal open, with literal restriction maps. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf
variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)

def opens : SectionPresheaf.Index U ⥤ X.Opens where
  obj := SectionPresheaf.openSubset U
  map := SectionPresheaf.arrow U hU
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

abbrev forgetScalars : ModuleCat.{u} Γ(X, U) ⥤ AddCommGrpCat.{u} := forget₂ _ _

def additiveFunctor : X.Modules ⥤ (SectionPresheaf.Index U)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf X.ringCatSheaf ⋙
    sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
      (Functor.whiskeringLeft (SectionPresheaf.Index U)ᵒᵖ X.Opensᵒᵖ AddCommGrpCat.{u}).obj (opens U hU).op

instance additive : (additiveFunctor U hU).Additive where
  map_add := rfl

def functorIso : ModuleFunctor.functor U hU ⋙
    (Functor.whiskeringRight (SectionPresheaf.Index U)ᵒᵖ (ModuleCat.{u} Γ(X, U)) AddCommGrpCat.{u}).obj
      (forgetScalars U) ≅ additiveFunctor U hU :=
  NatIso.ofComponents (fun M => NatIso.ofComponents (fun r => Iso.refl _) (by
    intro r s f
    rfl)) (by
      intro M N f
      apply NatTrans.ext
      funext r
      rfl)

variable (K : CochainComplex X.Modules ℕ)

abbrev linearComplex := ((ModuleFunctor.functor U hU).mapHomologicalComplex (.up ℕ)).obj K
abbrev additiveComplex := ((additiveFunctor U hU).mapHomologicalComplex (.up ℕ)).obj K

def complexIso : AugmentedCech.CoefficientTotal.mapped (forgetScalars U)
    (linearComplex U hU K) ≅ additiveComplex U hU K :=
  (NatIso.mapHomologicalComplex (functorIso U hU) (.up ℕ)).app K

variable {ι : Type u} [LinearOrder ι] (W : ι → SectionPresheaf.Index U)

local instance finiteBiproducts : HasFiniteBiproducts (ModuleCat.{u} Γ(X, U)) :=
  Abelian.hasFiniteBiproducts

def totalIso : ((forgetScalars U).mapHomologicalComplex (.up ℕ)).obj
    ((AugmentedOrdered.CechFunctor.bicomplex W (linearComplex U hU K)).total (.up ℕ)) ≅
      (AugmentedOrdered.CechFunctor.bicomplex W (additiveComplex U hU K)).total (.up ℕ) :=
  AugmentedCech.CoefficientTotal.totalIso W (forgetScalars U) (linearComplex U hU K) ≪≫
    HomologicalComplex₂.total.mapIso
      (((AugmentedOrdered.CechFunctor.functor W).mapHomologicalComplex (.up ℕ)).mapIso
        (complexIso U hU K)) (.up ℕ)

def homologyIso (q : ℕ) : (forgetScalars U).obj
    (((AugmentedOrdered.CechFunctor.bicomplex W (linearComplex U hU K)).total (.up ℕ)).homology q) ≅
      ((AugmentedOrdered.CechFunctor.bicomplex W (additiveComplex U hU K)).total (.up ℕ)).homology q :=
  ((((AugmentedOrdered.CechFunctor.bicomplex W (linearComplex U hU K)).total (.up ℕ)).sc q).mapHomologyIso
    (forgetScalars U)).symm ≪≫ homologyMapIso (totalIso U hU K W) q

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.AdditiveSections

import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.AdditiveSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.CoefficientHomology

/-! # Additive Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.AdditiveRestriction

noncomputable section

/-! The original additive principal-support restriction is the
scalar-forgotten affine-module restriction, also on actual cohomology. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.AdditiveSections
variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)
  (K : CochainComplex X.Modules ℕ)
  {ι : Type u} [LinearOrder ι] (W : ι → SectionPresheaf.Index U)

local instance finiteBiproducts : HasFiniteBiproducts (ModuleCat.{u} Γ(X, U)) :=
  Abelian.hasFiniteBiproducts

def ambientIso : ((AdditiveSections.forgetScalars U).mapHomologicalComplex (.up ℕ)).obj
    (AugmentedOrdered.CechForget.ambientComplex (AdditiveSections.linearComplex U hU K)) ≅ AugmentedOrdered.CechForget.ambientComplex (AdditiveSections.additiveComplex U hU K) :=
  (((CategoryTheory.evaluation (SectionPresheaf.Index U)ᵒᵖ AddCommGrpCat.{u}).obj
    (op (⊤_ SectionPresheaf.Index U))).mapHomologicalComplex (.up ℕ)).mapIso
      (AdditiveSections.complexIso U hU K)

theorem comparison : (AdditiveSections.totalIso U hU K W).hom ≫ AugmentedOrdered.CechForget.forgetSupport W (AdditiveSections.additiveComplex U hU K) =
    ((AdditiveSections.forgetScalars U).mapHomologicalComplex (.up ℕ)).map
      (AugmentedOrdered.CechForget.forgetSupport W (AdditiveSections.linearComplex U hU K)) ≫ (ambientIso U hU K).hom := by
  change (AugmentedCech.CoefficientTotal.totalIso W (AdditiveSections.forgetScalars U) (AdditiveSections.linearComplex U hU K)).hom ≫
    AugmentedOrdered.CechForgetNaturality.map W (AdditiveSections.complexIso U hU K).hom ≫
      AugmentedOrdered.CechForget.forgetSupport W (AdditiveSections.additiveComplex U hU K) = _
  rw [AugmentedOrdered.CechForgetNaturality.comparison,
    ← Category.assoc, AugmentedCech.CoefficientForget.comparison]
  rfl

def ambientHomologyIso (q : ℕ) : (AdditiveSections.forgetScalars U).obj
    ((AugmentedOrdered.CechForget.ambientComplex (AdditiveSections.linearComplex U hU K)).homology q) ≅
      (AugmentedOrdered.CechForget.ambientComplex (AdditiveSections.additiveComplex U hU K)).homology q :=
  (((AugmentedOrdered.CechForget.ambientComplex (AdditiveSections.linearComplex U hU K)).sc q).mapHomologyIso (AdditiveSections.forgetScalars U)).symm ≪≫
    homologyMapIso (ambientIso U hU K) q

theorem homology (q : ℕ) : (AdditiveSections.homologyIso U hU K W q).hom ≫
    homologyMap (AugmentedOrdered.CechForget.forgetSupport W (AdditiveSections.additiveComplex U hU K)) q =
      (AdditiveSections.forgetScalars U).map (homologyMap (AugmentedOrdered.CechForget.forgetSupport W (AdditiveSections.linearComplex U hU K)) q) ≫
        (ambientHomologyIso U hU K q).hom := by
  have h := congrArg (fun a => homologyMap a q) (comparison U hU K W)
  simp only [homologyMap_comp] at h
  let L := (AugmentedOrdered.CechFunctor.bicomplex W (AdditiveSections.linearComplex U hU K)).total (.up ℕ)
  let M := AugmentedOrdered.CechForget.ambientComplex (AdditiveSections.linearComplex U hU K)
  have hn : (AdditiveSections.forgetScalars U).map (homologyMap (AugmentedOrdered.CechForget.forgetSupport W (AdditiveSections.linearComplex U hU K)) q) ≫
      ((M.sc q).mapHomologyIso (AdditiveSections.forgetScalars U)).inv =
    ((L.sc q).mapHomologyIso (AdditiveSections.forgetScalars U)).inv ≫
      homologyMap (((AdditiveSections.forgetScalars U).mapHomologicalComplex (.up ℕ)).map
        (AugmentedOrdered.CechForget.forgetSupport W (AdditiveSections.linearComplex U hU K))) q :=
    ShortComplex.mapHomologyIso_inv_naturality
      ((shortComplexFunctor (ModuleCat.{u} Γ(X, U)) (.up ℕ) q).map
        (AugmentedOrdered.CechForget.forgetSupport W (AdditiveSections.linearComplex U hU K))) (AdditiveSections.forgetScalars U)
  change (((L.sc q).mapHomologyIso (AdditiveSections.forgetScalars U)).inv ≫
    homologyMap (AdditiveSections.totalIso U hU K W).hom q) ≫ _ = _
  rw [Category.assoc, h, ← Category.assoc]
  exact (congrArg (fun a => a ≫ homologyMap (ambientIso U hU K).hom q) hn.symm).trans
    (Category.assoc _ _ _)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.AdditiveRestriction

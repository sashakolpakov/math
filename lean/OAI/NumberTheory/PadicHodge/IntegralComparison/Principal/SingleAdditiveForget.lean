import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SingleAdditiveSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.AdditiveRestriction

/-! # Single Additive Forget -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SingleAdditiveForget

noncomputable section

/-! Forgetting the support of the original single survivor commutes
with the actual additive principal-section coordinates. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SingleAdditiveSections
open OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechForgetNaturality
variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)
  (S : X.Modules) (c : ℕ)

 def ambientIso : AugmentedOrdered.CechForget.ambientComplex (AdditiveSections.additiveComplex U hU (SingleAdditiveSections.moduleSingle S c)) ≅
    AugmentedOrdered.CechForget.ambientComplex (SingleAdditiveSections.sheafDiagram U hU S c) :=
  ((((CategoryTheory.evaluation (SectionPresheaf.Index U)ᵒᵖ AddCommGrpCat.{u}).obj
    (op (⊤_ SectionPresheaf.Index U))).mapHomologicalComplex (.up ℕ))).mapIso
      (SingleAdditiveSections.singleIso U hU S c)

 def ambientHomologyIso (q : ℕ) :=
  AdditiveRestriction.ambientHomologyIso U hU (SingleAdditiveSections.moduleSingle S c) q ≪≫
    homologyMapIso (ambientIso U hU S c) q

variable {ι : Type u} [LinearOrder ι] (W : ι → SectionPresheaf.Index U)

 theorem homology (q : ℕ) :
    (SingleAdditiveSections.homologyIso U hU S c W q).hom ≫
      homologyMap (AugmentedOrdered.CechForget.forgetSupport W (SingleAdditiveSections.sheafDiagram U hU S c)) q =
    (AdditiveSections.forgetScalars U).map
      (homologyMap (AugmentedOrdered.CechForget.forgetSupport W (AdditiveSections.linearComplex U hU (SingleAdditiveSections.moduleSingle S c))) q) ≫
      (ambientHomologyIso U hU S c q).hom := by
  change ((AdditiveSections.homologyIso U hU (SingleAdditiveSections.moduleSingle S c) W q).hom ≫
    homologyMap (AugmentedOrdered.CechForgetNaturality.map W (SingleAdditiveSections.singleIso U hU S c).hom) q) ≫
      homologyMap (AugmentedOrdered.CechForget.forgetSupport W (SingleAdditiveSections.sheafDiagram U hU S c)) q =
    (AdditiveSections.forgetScalars U).map
      (homologyMap (AugmentedOrdered.CechForget.forgetSupport W (AdditiveSections.linearComplex U hU (SingleAdditiveSections.moduleSingle S c))) q) ≫
        ((AdditiveRestriction.ambientHomologyIso U hU (SingleAdditiveSections.moduleSingle S c) q).hom ≫
          homologyMap (AugmentedOrdered.CechForgetNaturality.ambientMap (SingleAdditiveSections.singleIso U hU S c).hom) q)
  rw [Category.assoc, AugmentedOrdered.CechForgetNaturality.homology,
    ← Category.assoc, AdditiveRestriction.homology, Category.assoc]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SingleAdditiveForget

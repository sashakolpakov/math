import OAI.NumberTheory.PadicHodge.IntegralComparison.CommAlgebraicCechCohomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CechCup
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.SheafAugmentationProduct

/-! # Cech Algebra Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.CechAlgebraProduct

noncomputable section

/-! The original bounded crystalline algebra Čech complex has the
literal ambient-ring product in module-presheaf coordinates. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

private theorem trans_map_refl {D E : Type*} [Category* D] [Category* E]
    (G : D ⥤ E) {X : D} {Y : E} (e : Y ≅ G.obj X) :
    (e ≪≫ G.mapIso (Iso.refl X)).hom = e.hom := by
  exact (congrArg (fun a : G.obj X ⟶ G.obj X => e.hom ≫ a) (G.map_id X)).trans
    (Category.comp_id e.hom)

universe u

variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of B)) [IsSeparated f] (n : ℕ)
  {ι : Type u} (F : ι → BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)

local notation "CR" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "N" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve F

local instance coefficientProducts : HasProducts.{u} (ModuleCat.{u + 1} CR) :=
  fun T => (ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}).has_limits_of_shape (Discrete T)

local instance algebraProducts : HasProducts.{u} (CommAlgCat.{u + 1} CR) := by
  have h : HasLimitsOfSize.{u, u} (CommAlgCat.{u + 1} CR) :=
    hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} _
  exact fun T => h.has_limits_of_shape (Discrete T)

local instance forgetRing_preservesLimits :
    PreservesLimits (forget₂ (CommAlgCat.{u + 1} CR) CommRingCat.{u + 1}) := by
  change PreservesLimits ((commAlgCatEquivUnder (CommRingCat.of CR)).functor ⋙
    Under.forget (CommRingCat.of CR))
  infer_instance

local instance forgetModule_preservesLimits :
    PreservesLimits (CommAlgebraicCechPairing.forgetModule.{u + 1, u + 1} (R := CR)) := by
  have : PreservesLimits (CommAlgebraicCechPairing.forgetModule.{u + 1, u + 1} (R := CR) ⋙
      forget (ModuleCat.{u + 1} CR)) := by
    change PreservesLimits ((forget₂ (CommAlgCat.{u + 1} CR) CommRingCat.{u + 1}) ⋙
      forget CommRingCat.{u + 1})
    infer_instance
  exact preservesLimits_of_reflects_of_preserves _ (forget (ModuleCat.{u + 1} CR))

local instance forgetModule_preservesSmallLimits :
    PreservesLimitsOfSize.{u, u} (CommAlgebraicCechPairing.forgetModule.{u + 1, u + 1} (R := CR)) :=
  preservesLimitsOfSize_shrink.{u, u + 1, u, u + 1} _

def algebraPresheaf := (BoundedCrystalline.Site.inclusion (p := p) (J := J) (δ := δ) f n).op ⋙
  BoundedCrystalline.CechCup.structureAlgebraPresheaf f

def comparison : Cosimplicial.ModuleComplex.complex
    (BoundedCrystalline.CechCup.cochainAlgebra f n F) ≅
      BoundedFrame.CechComplex.presheafComplex f n F :=
  CommAlgebraicCechPairing.complexIso.{u + 1, u, u, u + 1, u + 1} N (algebraPresheaf f n)

theorem comparison_hom : (BoundedCrystalline.CechCup.comparison.{u} f n F).hom =
    (comparison.{u} f n F).hom :=
  trans_map_refl (NonemptyCechNerve.complexFunctor.{u + 1, u, u, u + 2, u + 1}
    (A := ModuleCat.{u + 1} CR) F)
    (X := BoundedFrame.SheafAugmentationProduct.ambient (p := p) (J := J) (δ := δ) f n)
    (comparison.{u} f n F)

abbrev cohomology_cup := CommAlgebraicCechCohomology.Pairing.cohomology_cup.{u + 1, u, u, u + 1, u + 1}
  N (algebraPresheaf f n)

omit [Fact p.Prime] [IsSeparated f] in
theorem multiplication (U : (BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)ᵒᵖ)
    (x y : (BoundedFrame.SheafAugmentationProduct.ambient f n).obj U) :
    CommAlgebraicCechPairing.multiplication
      (algebraPresheaf f n) U x y =
        BoundedFrame.SheafAugmentationProduct.ambientPairing f n U x y := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.CechAlgebraProduct

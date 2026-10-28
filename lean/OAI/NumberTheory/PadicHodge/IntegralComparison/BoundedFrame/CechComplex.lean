import OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Products
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.StructureDescent

/-! # Cech Complex -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.CechComplex

noncomputable section

/-! Actual bounded crystalline frame Čech cochains, with the original structure presheaf and sheaf. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction

universe u

variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) [IsSeparated f] (n : ℕ)
  {ι : Type u} (F : ι → BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)

local instance coefficientProducts : HasProducts.{u} (ModuleCat.{u + 1} R) := by
  let h : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} R) :=
    ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}
  exact fun I => h.has_limits_of_shape (Discrete I)

def ringComplex : CochainComplex (ModuleCat.{u} B) ℕ :=
  (NonemptyCechNerve.complexFunctor (A := ModuleCat.{u} B) F).obj
    ((BoundedCrystalline.Site.inclusion f n).op ⋙ BigCrystallineCohomology.modulePresheaf f)

def presheafComplex : CochainComplex (ModuleCat.{u + 1} R) ℕ :=
  (NonemptyCechNerve.complexFunctor (A := ModuleCat.{u + 1} R) F).obj
    ((BoundedCrystalline.Site.inclusion f n).op ⋙ BigCrystallineCohomology.largePresheaf f)

def complex : CochainComplex (ModuleCat.{u + 1} R) ℕ :=
  (NonemptyCechNerve.complexFunctor (A := ModuleCat.{u + 1} R) F).obj
    (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p) (J := J) (δ := δ) f n).obj

def presheafIso : presheafComplex f n F ≅ complex f n F :=
  (NonemptyCechNerve.complexFunctor (A := ModuleCat.{u + 1} R) F).mapIso
    (Functor.isoWhiskerLeft (BoundedCrystalline.Site.inclusion f n).op (Crystalline.StructureDescent.structurePresheafIso f))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.CechComplex

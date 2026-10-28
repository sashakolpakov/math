import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSection.Limit
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.SheafLinear

/-! # Reconstruction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSection.Reconstruction

noncomputable section

/-!
# IntegralComparison: original crystalline sections are compatible sections on every bounded level
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B))

theorem monotone_property : Monotone (BoundedCrystalline.Site.property (p := p) (J := J) (δ := δ) f) :=
  fun n m h _ hU => BoundedCrystalline.Site.property_mono f n m h hU

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)

def compatibleSections (M : Crystalline.ExactRestriction.ModuleSheaf (p := p) (J := J) (δ := δ) f) :
    Submodule R (∀ n, ExhaustivePresheafSections.Stage (BoundedCrystalline.Site.property f) (ModuleCat.of R R) M.obj n) :=
  ExhaustiveLinearSections.compatibleSubmodule R (BoundedCrystalline.Site.property f) (monotone_property f) (ModuleCat.of R R) M.obj

def homLinearEquiv (M : Crystalline.ExactRestriction.ModuleSheaf (p := p) (J := J) (δ := δ) f) :
    (BigCrystallineCohomology.constantUnit f ⟶ M) ≃ₗ[R] compatibleSections f M :=
  (LinearAdjunction.homLinearEquiv R (sheafificationAdjunction BigCrystallineSite.Object.topology (ModuleCat.{u + 1} R))
    ((Functor.const (BigCrystallineSite.Object p B J δ f)ᵒᵖ).obj (ModuleCat.of R R)) M).trans
      (ExhaustiveLinearSections.linearEquiv R (BoundedCrystalline.Site.property f) (monotone_property f)
        (BoundedCrystalline.Site.exists_level f) (ModuleCat.of R R) M.obj)

def degreeZeroLinearEquiv : BigCrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f 0 ≃ₗ[R]
    compatibleSections (p := p) (J := J) (δ := δ) f (BigCrystallineCohomology.structureSheaf f) :=
  Abelian.Ext.linearEquiv₀.trans (homLinearEquiv f (BigCrystallineCohomology.structureSheaf f))

def homLimitLinearEquiv (M : Crystalline.ExactRestriction.ModuleSheaf (p := p) (J := J) (δ := δ) f) :
    (BigCrystallineCohomology.constantUnit f ⟶ M) ≃ₗ[R]
      (limit (Limit.diagram R (BoundedCrystalline.Site.property f) (monotone_property f) (ModuleCat.of R R) M.obj) :
        ModuleCat.{u + 1} R) :=
  (homLinearEquiv f M).trans
    (Limit.limitIso R (BoundedCrystalline.Site.property f) (monotone_property f) (ModuleCat.of R R) M.obj).toLinearEquiv

def degreeZeroLimitLinearEquiv : BigCrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f 0 ≃ₗ[R]
    (limit (Limit.diagram R (BoundedCrystalline.Site.property (p := p) (J := J) (δ := δ) f) (monotone_property f)
      (ModuleCat.of R R) (BigCrystallineCohomology.structureSheaf f).obj) : ModuleCat.{u + 1} R) :=
  Abelian.Ext.linearEquiv₀.trans (homLimitLinearEquiv f (BigCrystallineCohomology.structureSheaf f))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSection.Reconstruction

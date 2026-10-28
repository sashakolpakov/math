import OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.FrameFreeModule
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.ProductSections

/-! # Zero Form Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedEtale.ZeroFormSections

noncomputable section

/-!
# IntegralComparison: sections of the original relative form presheaf are frame forms
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation

universe u

variable (p : ℕ) [Fact p.Prime] (k C σ : Type u) [Field k] [Fintype k] [CharP k p]
  [CommRing C] [Algebra k C] [LinearOrder σ] [Fintype σ]
  [Algebra (MvPolynomial σ k) C] [IsScalarTower k (MvPolynomial σ k) C]
  [Algebra.Etale (MvPolynomial σ k) C]

local notation "W" => WittVector p k
local notation "f" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k (OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation.affineScheme k C)
local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.ZeroLevel.LevelFrame.boundedFrame p k C
local notation "Q" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := Ideal.span {(p : W)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f 0
local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram.productDiagram F
local notation "π" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram.projection F
local notation "Index" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedEtale.ZeroFormPresheaf.Index σ

def freeProductIso (m : ℕ) : RelativeCrystalline.FreePresheaf.presheaf H (Index m) ≅
    (Over.star F ⋙ Over.forget F).op ⋙ RelativeCrystalline.FreePresheaf.presheaf Q (Index m) :=
  Iso.refl _

def formProductIso (m : ℕ) : RelativeCrystalline.ModuleMaps.formsPresheaf H Q π m ≅
    (Over.star F ⋙ Over.forget F).op ⋙ RelativeCrystalline.FreePresheaf.presheaf Q (Index m) :=
  (ZeroFormPresheaf.freeIso p k C σ m).symm ≪≫ freeProductIso p k C σ m

def homLinearEquiv (m : ℕ) :
    ((Functor.const (BoundedCrystalline.Site.Objects (p := p) (J := Ideal.span {(p : W)})
      (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f 0)ᵒᵖ).obj (ModuleCat.of W W) ⟶
        RelativeCrystalline.ModuleMaps.formsPresheaf H Q π m) ≃ₗ[W]
      RelativeFrame.FormMap.frameModule (F).obj m :=
  (Linear.homCongr W (Iso.refl _) (formProductIso p k C σ m)).trans
    ((Module.ProductSections.linearEquiv W F (RelativeCrystalline.FreePresheaf.presheaf Q (Index m))).trans
      (EtaleZero.FrameFreeModule.linearEquiv p k C σ m))

theorem formProductIso_app (m : ℕ)
    (U : BoundedCrystalline.Site.Objects (p := p) (J := Ideal.span {(p : W)})
      (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f 0)
    (ω : RelativeCrystalline.FormData.Forms H Q π U m) :
    (formProductIso p k C σ m).hom.app (op U) ω =
      (ZeroFormPresheaf.basis p k C σ U m).equivFun ω := rfl

theorem homLinearEquiv_apply (m : ℕ)
    (a : (Functor.const (BoundedCrystalline.Site.Objects (p := p) (J := Ideal.span {(p : W)})
      (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f 0)ᵒᵖ).obj (ModuleCat.of W W) ⟶
        RelativeCrystalline.ModuleMaps.formsPresheaf H Q π m) :
    homLinearEquiv p k C σ m a =
      EtaleZero.FrameFreeModule.linearEquiv p k C σ m
        (fun i => ((Q).map (prod.lift (𝟙 F) (𝟙 F))).ringMap
          ((ZeroFormPresheaf.basis p k C σ F m).equivFun (a.app (op F) (1 : W)) i)) := by
  have h := Module.ProductSections.linearEquiv_iso_apply W F
    (RelativeCrystalline.FreePresheaf.presheaf Q (Index m))
      (formProductIso p k C σ m) a
  exact (congrArg (EtaleZero.FrameFreeModule.linearEquiv p k C σ m) h).trans
    (congrArg (fun v : Index m → ((H).obj F).ring => EtaleZero.FrameFreeModule.linearEquiv p k C σ m
      (fun i => ((Q).map (prod.lift (𝟙 F) (𝟙 F))).ringMap (v i)))
        (formProductIso_app p k C σ m F (a.app (op F) (1 : W))))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedEtale.ZeroFormSections

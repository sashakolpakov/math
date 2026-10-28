import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameFreeModule
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.ProductSections

/-! # Witt Form Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSmooth.WittFormSections

noncomputable section

/-!
# IntegralComparison: sections of the original relative form presheaf are frame forms
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation

universe u

variable (p : ℕ) [Fact p.Prime] (k A C σ : Type u) [Field k] [CharP k p]
  [CommRing A] [Algebra (WittVector p k) A] [Module.Flat (WittVector p k) A]
  [CommRing C] [Algebra k C] [LinearOrder σ] [Fintype σ]
  [Algebra (MvPolynomial σ (WittVector p k)) A]
  [IsScalarTower (WittVector p k) (MvPolynomial σ (WittVector p k)) A]
  [Algebra.Etale (MvPolynomial σ (WittVector p k)) A]
  (ρ : A →+* C) (hρ : Function.Surjective ρ) (hker : RingHom.ker ρ = Ideal.span {(p : A)})
  (hbase : ∀ w : WittVector p k, ρ (algebraMap (WittVector p k) A w) =
    algebraMap k C (WittVector.constantCoeff w)) (n : ℕ)

local notation "W" => WittVector p k
local notation "f" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k (OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation.affineScheme k C)

local instance structureMap_separated : IsSeparated f :=
  WittFrameProduct.structureMap_separated p k C

local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.WittFrame.boundedFrame p k A C ρ hρ hker hbase n
local notation "Q" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := Ideal.span {(p : W)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f n
local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram.productDiagram F
local notation "π" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram.projection F
local notation "Index" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSmooth.WittFormPresheaf.Index σ

def freeProductIso (m : ℕ) : RelativeCrystalline.FreePresheaf.presheaf H (Index m) ≅
    (Over.star F ⋙ Over.forget F).op ⋙ RelativeCrystalline.FreePresheaf.presheaf Q (Index m) :=
  Iso.refl _

def formProductIso (m : ℕ) : RelativeCrystalline.ModuleMaps.formsPresheaf H Q π m ≅
    (Over.star F ⋙ Over.forget F).op ⋙ RelativeCrystalline.FreePresheaf.presheaf Q (Index m) :=
  (WittFormPresheaf.freeIso p k A C σ ρ hρ hker hbase n m).symm ≪≫ freeProductIso p k A C σ ρ hρ hker hbase n m

def homLinearEquiv (m : ℕ) :
    ((Functor.const (BoundedCrystalline.Site.Objects (p := p) (J := Ideal.span {(p : W)})
      (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f n)ᵒᵖ).obj (ModuleCat.of W W) ⟶
        RelativeCrystalline.ModuleMaps.formsPresheaf H Q π m) ≃ₗ[W]
      RelativeFrame.FormMap.frameModule (F).obj m :=
  (Linear.homCongr W (Iso.refl _) (formProductIso p k A C σ ρ hρ hker hbase n m)).trans
    ((IntegralComparison.Module.ProductSections.linearEquiv W F (RelativeCrystalline.FreePresheaf.presheaf Q (Index m))).trans
      (SmoothWitt.FrameFreeModule.linearEquiv p k A C σ ρ hρ hker hbase n m))

theorem formProductIso_app (m : ℕ)
    (U : BoundedCrystalline.Site.Objects (p := p) (J := Ideal.span {(p : W)})
      (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f n)
    (ω : RelativeCrystalline.FormData.Forms H Q π U m) :
    (formProductIso p k A C σ ρ hρ hker hbase n m).hom.app (op U) ω =
      (WittFormPresheaf.basis p k A C σ ρ hρ hker hbase n U m).equivFun ω := rfl

theorem homLinearEquiv_apply (m : ℕ)
    (a : (Functor.const (BoundedCrystalline.Site.Objects (p := p) (J := Ideal.span {(p : W)})
      (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f n)ᵒᵖ).obj (ModuleCat.of W W) ⟶
        RelativeCrystalline.ModuleMaps.formsPresheaf H Q π m) :
    homLinearEquiv p k A C σ ρ hρ hker hbase n m a =
      SmoothWitt.FrameFreeModule.linearEquiv p k A C σ ρ hρ hker hbase n m
        (fun i => ((Q).map (prod.lift (𝟙 F) (𝟙 F))).ringMap
          ((WittFormPresheaf.basis p k A C σ ρ hρ hker hbase n F m).equivFun (a.app (op F) (1 : W)) i)) := by
  have h := IntegralComparison.Module.ProductSections.linearEquiv_iso_apply W F
    (RelativeCrystalline.FreePresheaf.presheaf Q (Index m))
      (formProductIso p k A C σ ρ hρ hker hbase n m) a
  exact (congrArg (SmoothWitt.FrameFreeModule.linearEquiv p k A C σ ρ hρ hker hbase n m) h).trans
    (congrArg (fun v : Index m → ((H).obj F).ring => SmoothWitt.FrameFreeModule.linearEquiv p k A C σ ρ hρ hker hbase n m
      (fun i => ((Q).map (prod.lift (𝟙 F) (𝟙 F))).ringMap (v i)))
        (formProductIso_app p k A C σ ρ hρ hker hbase n m F (a.app (op F) (1 : W))))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSmooth.WittFormSections

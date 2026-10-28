import OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.FrameFreeModule
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.ProductSections

/-! # Form Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedTruncated.FormSections

noncomputable section

/-!
# IntegralComparison: sections of the original relative form presheaf are frame forms
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (A C σ : Type) [CommRing A] [CommRing C]
  [Algebra (Truncated.Witt.Ring p k n) A]
  [Algebra.Smooth (Truncated.Witt.Ring p k n) A] [Algebra k C]
  [LinearOrder σ] [Fintype σ]
  [Algebra (MvPolynomial σ (Truncated.Witt.Ring p k n)) A]
  [IsScalarTower (Truncated.Witt.Ring p k n)
    (MvPolynomial σ (Truncated.Witt.Ring p k n)) A]
  [Algebra.Etale (MvPolynomial σ (Truncated.Witt.Ring p k n)) A]
  (ρ : A →+* C) (hρ : Function.Surjective ρ)
  (hker : RingHom.ker ρ = Ideal.span {(p : A)})
  (hbase : ∀ w : WittVector p k,
    ρ (algebraMap (Truncated.Witt.Ring p k n) A (Truncated.Witt.quotient p k n w)) =
      algebraMap k C (WittVector.constantCoeff w))

local notation "W" => WittVector p k
local notation "f" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k (OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation.affineScheme k C)

local instance structureMap_separated : IsSeparated f :=
  FrameProduct.structureMap_separated p k C

local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.SmoothFrame.boundedFrame p A C ρ hρ hker k n hbase
local notation "Q" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := Ideal.span {(p : W)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f n
local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram.productDiagram F
local notation "π" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram.projection F
local notation "Index" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedTruncated.FormPresheaf.Index σ

def freeProductIso (m : ℕ) : RelativeCrystalline.FreePresheaf.presheaf H (Index m) ≅
    (Over.star F ⋙ Over.forget F).op ⋙ RelativeCrystalline.FreePresheaf.presheaf Q (Index m) :=
  Iso.refl _

def formProductIso (m : ℕ) : RelativeCrystalline.ModuleMaps.formsPresheaf H Q π m ≅
    (Over.star F ⋙ Over.forget F).op ⋙ RelativeCrystalline.FreePresheaf.presheaf Q (Index m) :=
  (FormPresheaf.freeIso p k n A C σ ρ hρ hker hbase m).symm ≪≫ freeProductIso p k n A C σ ρ hρ hker hbase m

def homLinearEquiv (m : ℕ) :
    ((Functor.const (BoundedCrystalline.Site.Objects (p := p) (J := Ideal.span {(p : W)})
      (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f n)ᵒᵖ).obj (ModuleCat.of W W) ⟶
        RelativeCrystalline.ModuleMaps.formsPresheaf H Q π m) ≃ₗ[W]
      RelativeFrame.FormMap.frameModule (F).obj m :=
  (Linear.homCongr W (Iso.refl _) (formProductIso p k n A C σ ρ hρ hker hbase m)).trans
    ((Module.ProductSections.linearEquiv W F (RelativeCrystalline.FreePresheaf.presheaf Q (Index m))).trans
      (Truncated.FrameFreeModule.linearEquiv p k n A C σ ρ hρ hker hbase m))

omit [Fintype k] in
theorem formProductIso_app (m : ℕ)
    (U : BoundedCrystalline.Site.Objects (p := p) (J := Ideal.span {(p : W)})
      (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f n)
    (ω : RelativeCrystalline.FormData.Forms H Q π U m) :
    (formProductIso p k n A C σ ρ hρ hker hbase m).hom.app (op U) ω =
      (FormPresheaf.basis p k n A C σ ρ hρ hker hbase U m).equivFun ω := rfl

omit [Fintype k] in
theorem homLinearEquiv_apply (m : ℕ)
    (a : (Functor.const (BoundedCrystalline.Site.Objects (p := p) (J := Ideal.span {(p : W)})
      (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f n)ᵒᵖ).obj (ModuleCat.of W W) ⟶
        RelativeCrystalline.ModuleMaps.formsPresheaf H Q π m) :
    homLinearEquiv p k n A C σ ρ hρ hker hbase m a =
      Truncated.FrameFreeModule.linearEquiv p k n A C σ ρ hρ hker hbase m
        (fun i => ((Q).map (prod.lift (𝟙 F) (𝟙 F))).ringMap
          ((FormPresheaf.basis p k n A C σ ρ hρ hker hbase F m).equivFun (a.app (op F) (1 : W)) i)) := by
  have h := Module.ProductSections.linearEquiv_iso_apply W F
    (RelativeCrystalline.FreePresheaf.presheaf Q (Index m))
      (formProductIso p k n A C σ ρ hρ hker hbase m) a
  exact (congrArg (Truncated.FrameFreeModule.linearEquiv p k n A C σ ρ hρ hker hbase m) h).trans
    (congrArg (fun v : Index m → ((H).obj F).ring => Truncated.FrameFreeModule.linearEquiv p k n A C σ ρ hρ hker hbase m
      (fun i => ((Q).map (prod.lift (𝟙 F) (𝟙 F))).ringMap (v i)))
        (formProductIso_app p k n A C σ ρ hρ hker hbase m F (a.app (op F) (1 : W))))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedTruncated.FormSections

import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameFunctor
import OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.ResolutionFunctor
import OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.OpenProducts
import OAI.NumberTheory.PadicHodge.IntegralComparison.CechCoefficient.Total
import OAI.AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi
import OAI.AlgebraicGeometry.Comparison.Betti.TotalExists

/-! # Padic Resolution Diagram -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PadicResolutionDiagram.IntrinsicPadicResolutionDiagram

noncomputable section

/-! The actual affine intersection frames assemble their relative crystalline
resolutions and natural augmentations into a Čech bicomplex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [Smooth X.hom]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (n : ℕ)

local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "JW" => Ideal.span {(p : WittVector p (ZMod p))}
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.ModuleSheaf (p := p) (J := JW) (δ := γ) w n

local instance separated : IsSeparated w := by
  dsimp only [IntegralComparison.Witt.Crystalline.wittStructureMap]
  infer_instance

def diagram : X.left.affineOpensᵒᵖ ⥤ CochainComplex S ℕ :=
  (FrameFunctor.IntrinsicPadicFrameFunctor.functor p X Y f hp n).op ⋙
    BoundedFrame.ResolutionFunctor.BoundedFrameResolutionFunctor.sheafFunctor w n

def augmentation : (Functor.const X.left.affineOpensᵒᵖ).obj
    ((CochainComplex.single₀ S).obj
      (IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p) (J := JW) (δ := γ) w n)) ⟶
        diagram p X Y f hp n :=
  Functor.whiskerLeft (FrameFunctor.IntrinsicPadicFrameFunctor.functor p X Y f hp n).op
    (BoundedFrame.ResolutionFunctor.BoundedFrameResolutionFunctor.augmentation w n)

def complex : CochainComplex (X.left.affineOpensᵒᵖ ⥤ S) ℕ :=
  AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (diagram p X Y f hp n)

def evaluationIso (U : X.left.affineOpens) :
    (((evaluation X.left.affineOpensᵒᵖ S).obj (op U)).mapHomologicalComplex (.up ℕ)).obj
      (complex p X Y f hp n) ≅
        IntegralComparison.Bounded.RelativeSheafComplex.complex w n
          (ChartImage.IntrinsicPadicOpenFrame.frame p X Y f hp U.val U.property n) :=
  AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.evaluationIso (.up ℕ) (diagram p X Y f hp n) (op U)

variable [X.left.IsSeparated] {ι : Type} (U : ι → X.left.affineOpens)

def bicomplex : HomologicalComplex₂ S (.up ℕ) (.up ℕ) :=
  IntegralComparison.CechCoefficient.Total.bicomplex (Affine.OpenProducts.AffineOpenProducts.nerve X.left U)
    (complex p X Y f hp n)

local instance finiteBiproducts : HasFiniteBiproducts S := HasFiniteBiproducts.of_hasFiniteProducts

local instance hasTotal : (bicomplex p X Y f hp n U).HasTotal (.up ℕ) :=
  AlgebraicGeometry.Comparison.Betti.TotalExists.hasTotal_of_finiteCoproducts _

def total : CochainComplex S ℕ := (bicomplex p X Y f hp n U).total (.up ℕ)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PadicResolutionDiagram.IntrinsicPadicResolutionDiagram

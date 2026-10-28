import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FrameFunctor
import OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.ResolutionFunctor
import OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.OpenProducts
import OAI.NumberTheory.PadicHodge.IntegralComparison.CechCoefficient.Total
import OAI.AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi
import OAI.AlgebraicGeometry.Comparison.Betti.TotalExists

/-! # Resolution Diagram -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ResolutionDiagram

noncomputable section

/-! The actual affine intersection frames assemble their relative crystalline
resolutions and natural augmentations into a Čech bicomplex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [Smooth X.hom]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))

local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y
local notation "JW" => Ideal.span {(p : WittVector p k)}
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.ModuleSheaf (p := p) (J := JW) (δ := γ) w n

local instance separated : IsSeparated w := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance

def diagram : X.left.affineOpensᵒᵖ ⥤ CochainComplex S ℕ :=
  (FrameFunctor.functor p k n X Y f hp).op ⋙
    GeometricComparison.BoundedFrame.ResolutionFunctor.BoundedFrameResolutionFunctor.sheafFunctor w n

def augmentation : (Functor.const X.left.affineOpensᵒᵖ).obj
    ((CochainComplex.single₀ S).obj
      (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p) (J := JW) (δ := γ) w n)) ⟶
        diagram p k n X Y f hp :=
  Functor.whiskerLeft (FrameFunctor.functor p k n X Y f hp).op
    (GeometricComparison.BoundedFrame.ResolutionFunctor.BoundedFrameResolutionFunctor.augmentation w n)

def complex : CochainComplex (X.left.affineOpensᵒᵖ ⥤ S) ℕ :=
  AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (diagram p k n X Y f hp)

def evaluationIso (U : X.left.affineOpens) :
    (((evaluation X.left.affineOpensᵒᵖ S).obj (op U)).mapHomologicalComplex (.up ℕ)).obj
      (complex p k n X Y f hp) ≅
        Bounded.RelativeSheafComplex.complex w n
          (Truncated.AffineModelFrame.frame p k n X Y f hp U.val U.property) :=
  AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.evaluationIso (.up ℕ) (diagram p k n X Y f hp) (op U)

variable [X.left.IsSeparated] {ι : Type} (U : ι → X.left.affineOpens)

def bicomplex : HomologicalComplex₂ S (.up ℕ) (.up ℕ) :=
  CechCoefficient.Total.bicomplex (NonemptyCechNerve.nerve U)
    (complex p k n X Y f hp)

local instance finiteBiproducts : HasFiniteBiproducts S := HasFiniteBiproducts.of_hasFiniteProducts

local instance hasTotal : (bicomplex p k n X Y f hp U).HasTotal (.up ℕ) :=
  AlgebraicGeometry.Comparison.Betti.TotalExists.hasTotal_of_finiteCoproducts _

def total : CochainComplex S ℕ := (bicomplex p k n X Y f hp U).total (.up ℕ)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ResolutionDiagram

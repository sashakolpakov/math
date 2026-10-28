import OAI.NumberTheory.PadicHodge.GeometricComparison.Section.ComplexBifunctor
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PadicResolutionDiagram
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionComplex

/-! # Section Bifunctor -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionBifunctor.IntrinsicPadicSectionBifunctor

noncomputable section

/-! The actual native frame resolution and original Zariski section
functors give a strict bifunctor on integral affine opens. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (n : ℕ)

local notation "W" => WittVector p (ZMod p)
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)
local notation "Rcoeff" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))

local instance separated : IsSeparated w := by
  dsimp only [IntegralComparison.Witt.Crystalline.wittStructureMap]
  infer_instance

def specialOpens : X.left.affineOpens ⥤ Y.left.Opens :=
  Affine.OpenProducts.AffineOpenProducts.inclusion X.left ⋙ TopologicalSpace.Opens.map f.base

def sections := IntegralComparison.BoundedOpen.SectionComplex.functor (p := p)
  (J := Ideal.span {(p : W)}) (δ := γ) w n ⋙
    (Functor.whiskeringLeft X.left.affineOpensᵒᵖ Y.left.Opensᵒᵖ (ModuleCat.{2} Rcoeff)).obj
      (specialOpens p X Y f).op

instance sections_additive : (sections p X Y f n).Additive := by
  dsimp only [sections]
  infer_instance

def rows : X.left.affineOpensᵒᵖ ⥤ X.left.affineOpensᵒᵖ ⥤ CochainComplex (ModuleCat.{2} Rcoeff) ℕ :=
  Section.ComplexBifunctor.SectionComplexBifunctor.functor (sections p X Y f n)
    (PadicResolutionDiagram.IntrinsicPadicResolutionDiagram.diagram p X Y f hp n)

def rowIso (I : X.left.affineOpens) : (rows p X Y f hp n).obj (op I) ≅
    PadicResolutionDiagram.IntrinsicPadicResolutionDiagram.diagram p X Y f hp n ⋙
      (IntegralComparison.BoundedOpen.SectionComplex.functor (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n ⋙
        IntegralComparison.BoundedOpen.SectionComplex.evaluation (B := W) (f ⁻¹ᵁ I.val)).mapHomologicalComplex (.up ℕ) :=
  Section.ComplexBifunctor.SectionComplexBifunctor.rowIso (sections p X Y f n)
    (PadicResolutionDiagram.IntrinsicPadicResolutionDiagram.diagram p X Y f hp n) (op I)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionBifunctor.IntrinsicPadicSectionBifunctor

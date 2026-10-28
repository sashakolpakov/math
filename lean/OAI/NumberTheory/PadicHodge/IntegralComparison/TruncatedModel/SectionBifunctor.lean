import OAI.NumberTheory.PadicHodge.GeometricComparison.Section.ComplexBifunctor
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ResolutionDiagram
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionComplex

/-! # Section Bifunctor -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SectionBifunctor

noncomputable section

/-! The actual native frame resolution and original Zariski section
functors give a strict bifunctor on integral affine opens. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))

local notation "W" => WittVector p k
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "Rcoeff" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)

local instance separated : IsSeparated w := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance

def specialOpens : X.left.affineOpens ⥤ Y.left.Opens :=
  GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion X.left ⋙ TopologicalSpace.Opens.map f.base

def sections := BoundedOpen.SectionComplex.functor (p := p)
  (J := Ideal.span {(p : W)}) (δ := γ) w n ⋙
    (Functor.whiskeringLeft X.left.affineOpensᵒᵖ Y.left.Opensᵒᵖ (ModuleCat.{2} Rcoeff)).obj
      (specialOpens p k n X Y f).op

instance sections_additive : (sections p k n X Y f).Additive := by
  dsimp only [sections]
  infer_instance

def rows : X.left.affineOpensᵒᵖ ⥤ X.left.affineOpensᵒᵖ ⥤ CochainComplex (ModuleCat.{2} Rcoeff) ℕ :=
  GeometricComparison.Section.ComplexBifunctor.SectionComplexBifunctor.functor (sections p k n X Y f)
    (ResolutionDiagram.diagram p k n X Y f hp)

def rowIso (I : X.left.affineOpens) : (rows p k n X Y f hp).obj (op I) ≅
    ResolutionDiagram.diagram p k n X Y f hp ⋙
      (BoundedOpen.SectionComplex.functor (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n ⋙
        BoundedOpen.SectionComplex.evaluation (B := W) (f ⁻¹ᵁ I.val)).mapHomologicalComplex (.up ℕ) :=
  GeometricComparison.Section.ComplexBifunctor.SectionComplexBifunctor.rowIso (sections p k n X Y f)
    (ResolutionDiagram.diagram p k n X Y f hp) (op I)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SectionBifunctor

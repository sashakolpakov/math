import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.BoundedFamilyIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalIn
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.FamilyIsoSections

/-! # Principal Transported Family -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalTransportedFamily.Family

noncomputable section

/-! Two native principal families, compared on the same coefficient
category and the same original special-fiber opens. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ)
  (X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X₁.hom] [Smooth X₁.hom] [X₁.left.IsSeparated]
  [IsProper X₂.hom] [Smooth X₂.hom] [X₂.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom]
  (f₁ : Y.left ⟶ X₁.left) (f₂ : Y.left ⟶ X₂.left)
  (hp₁ : IsPullback f₁ Y.hom X₁.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (hp₂ : IsPullback f₂ Y.hom X₂.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (U₁ : X₁.left.affineOpens) (U₂ : X₂.left.affineOpens)
  (e : (SmallFrame.functor p k n X₂ Y f₂ hp₂).obj U₂ ≅
    (SmallFrame.functor p k n X₁ Y f₁ hp₁).obj U₁)

local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y
local notation "C" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFrame.Index X₁.left U₁
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFamilyIso.Family.reindex p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e
local notation "G₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalIn.Family.frames p k n X₁ Y f₁ hp₁ U₁
local notation "G₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalIn.Family.frames p k n X₂ Y f₂ hp₂ U₂
local notation "F₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalIn.Family.center p k n X₁ Y f₁ hp₁ U₁
local notation "F₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalIn.Family.center p k n X₂ Y f₂ hp₂ U₂
local notation "O" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalIn.Family.opens p k n X₁ Y f₁ U₁
local notation "Q" => OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.ResolutionFunctor.BoundedFrameResolutionFunctor.sheafFunctor (p := p)
  (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) w n
local notation "ρ₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalIn.Family.cone p k n X₁ Y f₁ hp₁ U₁
local notation "ρ₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalIn.Family.cone p k n X₂ Y f₂ hp₂ U₂

local instance globalSeparated : IsSeparated w := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance

abbrev frames := (R).op ⋙ G₂

def iso : G₁ ≅ frames p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e :=
  BoundedFamilyIso.Family.oppositeIso p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e

def baseIso : F₁ ≅ F₂ :=
  (BoundedFamilyIso.Family.baseIso p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e).op

def cone : (Functor.const Cᵒᵖ).obj F₂ ⟶ frames p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e where
  app r := (ρ₂).app ((R).op.obj r)
  naturality _ _ a := (ρ₂).naturality ((R).op.map a)

omit [IsProper X₁.hom] [X₁.left.IsSeparated] [IsProper X₂.hom] [X₂.left.IsSeparated] [IsSeparated Y.hom] in
theorem projection_square (r : Cᵒᵖ) :
    (ρ₁).app r ≫ (iso p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e).hom.app r =
      (baseIso p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e).hom ≫
        (cone p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e).app r :=
  congrArg Quiver.Hom.op
    (BoundedFamilyIso.Family.projection_square p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e r.unop)

local instance sourceRestrictionIso : IsIso (GeometricComparison.FixedDiagramTransformation.FixedDiagramSections.map
    (BoundedFrame.FamilySections.Family.sections w n O) ((Q).obj F₁)
    (BoundedFrame.FamilySections.Family.diagram w n G₁)
    (BoundedFrame.FamilySections.Family.cone w n F₁ ρ₁)) :=
  PrincipalIn.Family.fixed_isIso p k n X₁ Y f₁ hp₁ U₁

abbrev restriction_isIso := BoundedFrame.FamilyIsoSections.Family.fixed_isIso w n O
  (iso p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e)
  (baseIso p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e) ρ₁
  (cone p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e)
  (projection_square p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e)

abbrev naturality := BoundedFrame.FamilyIsoSections.Family.naturality w n O
  (iso p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e)
  (baseIso p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e) ρ₁
  (cone p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e)
  (projection_square p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalTransportedFamily.Family

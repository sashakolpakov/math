import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.LocalPDNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.IncomingSectionReindex
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSection.FamilyCoordinates

/-! # Local Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.LocalCoordinates.Comparison

noncomputable section

/-! The local PD map and the incoming comparison use the same frame
map and the same canonical change of principal-open section family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem replace_right {C : Type*} [Category C] {A B D E : C}
    (u : A ⟶ B) (v : B ⟶ D) (r r' : D ⟶ E) (w : A ⟶ E)
    (hr : r' = r) (h : u ≫ (v ≫ r') = w) : (u ≫ v) ≫ r = w :=
  (congrArg (fun q => (u ≫ v) ≫ q) hr.symm).trans ((Category.assoc _ _ _).trans h)

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

local notation "K₂" => Functor.obj (OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ResolutionDiagram.diagram p k n X₂ Y f₂ hp₂) (op U₂)
local notation "s" => NatIso.mapHomologicalComplex
  (IncomingSectionReindex.sectionIso p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e) (ComplexShape.up ℕ)
local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalCoefficientNaturality.restriction p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e
local notation "a" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalCoefficientNaturality.sourceIso p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y

local instance globalSeparated : IsSeparated w := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance

omit [IsProper X₁.hom] [X₁.left.IsSeparated] [IsProper X₂.hom] [X₂.left.IsSeparated] in
theorem frame_map : LocalPrincipal.Sections.baseMap p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e =
    IncomingSectionHomotopy.frameMap p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e := rfl

abbrev section_change :=
  BoundedSection.FamilyCoordinates.Family.comparison w n
    (PrincipalFamilyIso.Family.reindex p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e)
    (PrincipalSections.opens p k n X₁ Y f₁ U₁)
    (PrincipalSections.opens p k n X₂ Y f₂ U₂)
    (IncomingSectionReindex.family_eq p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e)
    (PrincipalOpenFunctorEq.opens_eq p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e).symm K₂

abbrev pd_square := replace_right _ _ ((s).app K₂).hom _ _
  (section_change p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e)
  (LocalPDNaturality.naturality p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.LocalCoordinates.Comparison

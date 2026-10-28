import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.IncomingReindex
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.IncomingSectionHomotopy
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalOpensIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalCoefficientNaturality

/-! # Incoming Section Reindex -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.IncomingSectionReindex

noncomputable section

/-! The transported native incoming comparison is exactly the
reindexed comparison on its own principal-open family. -/

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
local notation "r" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFamilyIso.Family.reindex p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e
local notation "F₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalSections.opens p k n X₁ Y f₁ U₁
local notation "F₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalSections.opens p k n X₂ Y f₂ U₂
local notation "V₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.LocalIncomingHomotopy.preimage f₁ U₁
local notation "V₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.LocalIncomingHomotopy.preimage f₂ U₂
local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalCoefficientNaturality.restriction p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e

omit [IsProper X₁.hom] [X₁.left.IsSeparated] [IsProper X₂.hom] [X₂.left.IsSeparated] [IsSeparated Y.hom] in
theorem family_eq : F₁ = BoundedOpen.IncomingMap.reindexedOpens F₂ r := by
  apply OrderHom.ext
  funext t
  exact (PrincipalOpensIso.opens_apply p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e t).symm

def sectionIso := BoundedOpen.IncomingMap.familyIso (p := p)
  (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
  w n F₁ (BoundedOpen.IncomingMap.reindexedOpens F₂ r)
    (family_eq p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e)

variable (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
  (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
  (Witt.Crystalline.wittStructureMap p k Y) n))

local notation "K₂" => Functor.obj (OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ResolutionDiagram.diagram p k n X₂ Y f₂ hp₂) (op U₂)
local notation "s" => NatIso.mapHomologicalComplex
  (sectionIso p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e) (ComplexShape.up ℕ)

abbrev comparison :=
  BoundedOpen.IncomingReindex.comparison w n V₁ V₂
    (LocalIncomingHomotopy.opens_eq p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e)
    F₂ F₁ r (PrincipalSections.le_chart p k n X₂ Y f₂ U₂)
    (PrincipalSections.le_chart p k n X₁ Y f₁ U₁)
    (family_eq p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e) K₂ I.cocomplex
    (IncomingFrame.comparison p k n X₂ Y f₂ hp₂ U₂ I)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.IncomingSectionReindex

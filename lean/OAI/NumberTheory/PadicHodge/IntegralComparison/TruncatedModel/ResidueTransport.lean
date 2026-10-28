import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ResidueTransportForms
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SupportedReindexBase
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechReindexCoefficientTop

/-! # Residue Transport -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ResidueTransport

noncomputable section

/-! The original native source map carries the literal supported
residue class to the residue for the ambient images of its parameters. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

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

local notation "Q₁" => Functor.obj (OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SmallFrame.functor p k n X₁ Y f₁ hp₁) U₁
local notation "r" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFamilyIso.Family.reindex p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e
local notation "s" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalCoefficientNaturality.sourceIso p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e
local notation "K₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.Principal.Comparison.source p k n X₁ Y f₁ hp₁ U₁
local notation "K₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.Principal.Comparison.source p k n X₂ Y f₂ hp₂ U₂

variable (g : ℕ) (b : Fin g → Γ(X₁.left, U₁.val))
local notation "U" => OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.PDComplex.family p k Y Q₁ g b
local notation "b₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ResidueTransportForms.parameters p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e g b

abbrev image_coordinates :=
  (congrArg (fun z => (AugmentedOrdered.CechReindexTop.coefficient r U g (by simp) ((K₂).X g)).hom z)
    (ResidueTransportForms.source_coordinates p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e g b)).trans
    (ResidueTransportForms.reindex_coordinates p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e g b)

omit [IsProper X₁.hom] [X₁.left.IsSeparated] [IsProper X₂.hom] [X₂.left.IsSeparated] [IsSeparated Y.hom] in
theorem residue_class :
    HomologicalComplex.homologyMap
      (SupportedReindexBase.sourceMap p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e g b) (g+g)
      (ResidueClass.residueClass p k n X₁ Y f₁ hp₁ U₁ g b) =
    ResidueClass.residueClass p k n X₂ Y f₂ hp₂ U₂ g b₂ :=
  AugmentedOrdered.CechReindexCoefficientTop.homology_of_image_eq r U K₁ K₂ (s).hom g (by simp) g
    (ResidueClass.form p k n X₁ Y f₁ hp₁ U₁ g b)
    (ResidueClass.form_closed p k n X₁ Y f₁ hp₁ U₁ g b)
    (ResidueClass.form p k n X₂ Y f₂ hp₂ U₂ g b₂)
    (ResidueClass.form_closed p k n X₂ Y f₂ hp₂ U₂ g b₂)
    (image_coordinates p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e g b)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ResidueTransport

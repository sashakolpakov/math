import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SupportedReindexData
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ResidueClass
import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.PDReindexTop

/-! # Residue Transport Forms -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ResidueTransportForms

noncomputable section

/-! Exact logarithmic-form coordinates for transporting the literal
native residue between isomorphic smooth crystalline frames. -/

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
local notation "Q₂" => Functor.obj (OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SmallFrame.functor p k n X₂ Y f₂ hp₂) U₂
local notation "r" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFamilyIso.Family.reindex p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e
local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalCoefficientNaturality.restriction p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e
local notation "s" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalCoefficientNaturality.sourceIso p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e
local notation "L₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.Principal.Comparison.source p k n X₂ Y f₂ hp₂ U₂

abbrev transportedComplex := ((H).mapHomologicalComplex (.up ℕ)).obj L₂

variable (g : ℕ) (b : Fin g → Γ(X₁.left, U₁.val))

local notation "U" => OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.PDComplex.family p k Y Q₁ g b

def parameters : Fin g → Γ(X₂.left, U₂.val) := Supported.PDReindexTop.parameters p k Y e g b

def intermediateForm :
    ((transportedComplex p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e).X g).obj
      (op (Supported.PDComplex.topCoefficient p k Y Q₁ g b)) :=
  ⟨⟨Supported.PDFrameIso.logarithmicForm p k Y e g b⟩⟩

omit [IsProper X₁.hom] [X₁.left.IsSeparated] [IsProper X₂.hom] [X₂.left.IsSeparated] [IsSeparated Y.hom] in
theorem source_coordinates :
    ((s).hom.f g).app (op (Supported.PDComplex.topCoefficient p k Y Q₁ g b))
      (ResidueClass.form p k n X₁ Y f₁ hp₁ U₁ g b) =
      intermediateForm p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e g b :=
  congrArg (fun z => ULift.up.{2,1} (ULift.up.{1,0} z))
    (Supported.PDFrameIso.map_logarithmicForm p k Y e g b)

omit [IsProper X₁.hom] [X₁.left.IsSeparated] [IsProper X₂.hom] [X₂.left.IsSeparated] [IsSeparated Y.hom] in
theorem reindex_coordinates :
    AugmentedOrdered.CechReindexTop.coefficient r U g (by simp) ((L₂).X g)
      (intermediateForm p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e g b) =
      ResidueClass.form p k n X₂ Y f₂ hp₂ U₂ g
        (parameters p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e g b) :=
  congrArg (fun z => ULift.up.{2,1} (ULift.up.{1,0} z))
    (Supported.PDReindexTop.map_logarithmicForm p k Y e g b)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ResidueTransportForms

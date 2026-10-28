import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalPDNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalCoefficientComponent

/-! # Principal Coefficient Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalCoefficientNaturality

noncomputable section

/-! The actual principal comparison coefficient map is natural under
the normalized change of native local lift. -/
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
local notation "C" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFrame.Index X₁.left U₁
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFamilyIso.Family.reindex p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e
local notation "P₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Diagram.functor X₁.left U₁.val U₁.property
local notation "P₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Diagram.functor X₂.left U₂.val U₂.property

local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)
local notation "L" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.Principal.Comparison.coefficients p k

def restriction :
    ((PrincipalFrame.Index X₂.left U₂)ᵒᵖ ⥤ ModuleCat.{2} A) ⥤
    (Cᵒᵖ ⥤ ModuleCat.{2} A) :=
  (Functor.whiskeringLeft _ _ _).obj (R).op

instance restriction_additive : (restriction p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e).Additive where
  map_add := rfl

def sourceIso : Principal.Comparison.source p k n X₁ Y f₁ hp₁ U₁ ≅
    ((restriction p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e).mapHomologicalComplex (.up ℕ)).obj
      (Principal.Comparison.source p k n X₂ Y f₂ hp₂ U₂) :=
  ((GeometricComparison.ComplexAssemblyPresheaves.ComplexAssemblyCoefficients.presheaves (T := Cᵒᵖ) (L)).mapHomologicalComplex (.up ℕ)).mapIso
    (Supported.PDFrameIso.complexIso p k Y e)

def diagramIso :
    (P₁).op ⋙ FrameDiagonalMap.source p k n X₁ Y f₁ hp₁ ≅
    (R).op ⋙ (P₂).op ⋙ FrameDiagonalMap.source p k n X₂ Y f₂ hp₂ :=
  Functor.isoWhiskerRight
    (PrincipalPDNaturality.diagramIso p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e)
    ((L).mapHomologicalComplex (.up ℕ))

def reindexedMap :
    ((restriction p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e).mapHomologicalComplex (.up ℕ)).obj
      (Principal.Comparison.source p k n X₂ Y f₂ hp₂ U₂) ⟶
    AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ)
      ((R).op ⋙ (P₂).op ⋙ FrameDiagonalMap.source p k n X₂ Y f₂ hp₂) :=
  ((restriction p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e).mapHomologicalComplex (.up ℕ)).map
    (Principal.Comparison.coefficientMap p k n X₂ Y f₂ hp₂ U₂)

omit [IsProper X₁.hom] [X₁.left.IsSeparated] [IsProper X₂.hom] [X₂.left.IsSeparated] [IsSeparated Y.hom] in
theorem naturality :
    Principal.Comparison.coefficientMap p k n X₁ Y f₁ hp₁ U₁ ≫
      AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.map (.up ℕ) (diagramIso p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e).hom =
    (sourceIso p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e).hom ≫
      reindexedMap p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply NatTrans.ext
  funext r
  have h := congrArg (fun a => (L).map a)
    (PrincipalPDNaturality.Square.component p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e q r.unop)
  rw [Functor.map_comp, Functor.map_comp] at h
  change ((Principal.Comparison.coefficientMap p k n X₁ Y f₁ hp₁ U₁).f q).app r ≫ _ =
    _ ≫ ((Principal.Comparison.coefficientMap p k n X₂ Y f₂ hp₂ U₂).f q).app ((R).op.obj r)
  rw [PrincipalCoefficientComponent.component,
    PrincipalCoefficientComponent.component]
  exact h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalCoefficientNaturality

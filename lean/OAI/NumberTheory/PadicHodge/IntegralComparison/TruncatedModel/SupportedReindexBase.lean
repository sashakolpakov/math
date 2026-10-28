import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SupportedReindexGeometry
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSupported.CechCoefficientReindex

/-! # Supported Reindex Base -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SupportedReindexBase

noncomputable section

/-! The original principal coefficient isomorphism and its literal
change of opens transport the supported comparison into bounded cohomology. -/

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

local notation "r" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFamilyIso.Family.reindex p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e
local notation "F₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.Supported.Comparison.opens p k n X₁ Y f₁ U₁
local notation "F₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.Supported.Comparison.opens p k n X₂ Y f₂ U₂
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)

local notation "L" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.Supported.Comparison.source p k n X₁ Y f₁ hp₁ U₁
local notation "M" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.Supported.Comparison.source p k n X₂ Y f₂ hp₂ U₂
local notation "a" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalCoefficientNaturality.sourceIso p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e
local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalCoefficientNaturality.restriction p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e

variable (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
  (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
  (Witt.Crystalline.wittStructureMap p k Y) n))

local notation "m" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.Supported.Comparison.coefficientMap p k n X₂ Y f₂ hp₂ U₂ I

def coefficientMap := BoundedSupported.CechCoefficientReindex.coefficientMap w n I r F₁ F₂
  (SupportedReindexData.opens_eq p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e)
  L M (a).hom m

variable (g : ℕ) (b : Fin g → Γ(X₁.left, U₁.val))

local notation "V" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.Supported.Comparison.family p k n X₁ U₁ g b
local notation "b₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SupportedReindexData.coefficients p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e g b

def sourceMap := BoundedSupported.CechCoefficientReindex.sourceMap r V L M (a).hom

variable (O : Y.left.Opens)
  (hO : ∀ i, (Supported.Comparison.opens p k n X₁ Y f₁ U₁).obj
    (Supported.Comparison.family p k n X₁ U₁ g b i) ≤ O)
  (hcover : (Supported.Comparison.opens p k n X₁ Y f₁ U₁).obj
    (⊤_ (PrincipalFrame.Index X₁.left U₁)) ⊓ O ≤
      ⨆ i, (Supported.Comparison.opens p k n X₁ Y f₁ U₁).obj
        (Supported.Comparison.family p k n X₁ U₁ g b i))
  (hglobal : (Supported.Comparison.opens p k n X₁ Y f₁ U₁).obj
    (⊤_ (PrincipalFrame.Index X₁.left U₁)) ⊔ O = ⊤)

local notation "rows₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SupportedRows.exactAt_succ p k n X₁ Y f₁ U₁ I g b
local notation "rows₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SupportedRows.exactAt_succ p k n X₂ Y f₂ U₂ I g b₂
local notation "hO₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SupportedReindexGeometry.below p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e g b O hO
local notation "hcover₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SupportedReindexGeometry.cover p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e g b O hcover
local notation "hglobal₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SupportedReindexGeometry.global p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e O hglobal

omit [IsProper X₁.hom] [X₁.left.IsSeparated] in
theorem comparison (i : ℕ) :
    BoundedSupported.Cech.map w n I F₁ V O hO hcover rows₁ hglobal L
      (coefficientMap p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e I) i =
      HomologicalComplex.homologyMap (sourceMap p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e g b) i ≫
        Supported.Comparison.toBounded p k n X₂ Y f₂ hp₂ U₂ I
          g b₂ O hO₂ hcover₂ rows₂ hglobal₂ i :=
  BoundedSupported.CechCoefficientReindex.comparison w n I r F₁ F₂
    (SupportedReindexData.opens_eq p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e)
    V L M (a).hom m O hO hO₂ hcover hcover₂ rows₁
    (SupportedReindexGeometry.rows p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e g b I)
    hglobal hglobal₂ i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SupportedReindexBase

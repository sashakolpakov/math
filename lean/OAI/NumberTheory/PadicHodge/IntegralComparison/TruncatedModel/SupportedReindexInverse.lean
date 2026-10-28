import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SupportedReindexBase

/-! # Supported Reindex Inverse -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SupportedReindexInverse

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

def coefficientPrefix := (a).hom ≫ ((H).mapHomologicalComplex (.up ℕ)).map m

def canonicalPrefix := (a).hom ≫
  BoundedSupported.CechMapReindex.pulledMap w n I r F₂ M m

omit [IsProper X₁.hom] [X₁.left.IsSeparated] in
theorem prefix_eq :
    coefficientPrefix p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e I =
      canonicalPrefix p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e I := rfl

def canonicalOpenChange :=
  eqToHom (congrArg
    (fun F => Supported.OrderedCechEdge.presheafComplex.{1,0,0,2} R Y.left.carrier F
      (BoundedOpen.FlasqueComplex.complex w n I))
    (SupportedReindexData.opens_eq p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e).symm)

def originalTransport :=
  coefficientPrefix p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e I ≫
    ((NatIso.mapHomologicalComplex
      (IncomingSectionReindex.sectionIso p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e)
      (.up ℕ)).app I.cocomplex).inv

def canonicalTransport :=
  canonicalPrefix p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e I ≫
    canonicalOpenChange p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e I

omit [IsProper X₁.hom] [X₁.left.IsSeparated] in
theorem canonicalTransport_eq :
    canonicalTransport p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e I =
      SupportedReindexBase.coefficientMap p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e I := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SupportedReindexInverse

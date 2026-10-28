import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SupportedNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ResidueTransport
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SupportedResidue
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SupportedSection

/-! # Supported Residue Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SupportedResidueNaturality

noncomputable section

/-! The literal supported logarithmic residue gives the same class
in the original bounded crystalline cohomology after changing its
smooth model by the prescribed crystalline frame isomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem apply_composite {R : Type*} [CommRing R] {M N P : ModuleCat R}
    {f : M ⟶ P} {s : M ⟶ N} {g : N ⟶ P}
    (h : f = s ≫ g) {x : M} {y : N} (hx : s x = y) : f x = g y := by
  subst f
  change g (s x) = g y
  exact congrArg (fun z => g z) hx

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
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y) n))
  (j : AlgebraicGeometry.Crystalline.Cohomology.Base.SmoothProperEtaleCover.BaseSmoothProperEtaleCover.Index (Truncated.Witt.Ring p k n) X₁)
  (hj : U₁.val ≤ AlgebraicGeometry.Crystalline.Cohomology.Base.ProperOrdinaryFormCharts.BaseSmoothProperOrdinaryFormCharts.opens (Truncated.Witt.Ring p k n) X₁ j)

local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y
local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.Supported.Comparison.opens p k n X₁ Y f₁ U₁
local notation "K" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.Supported.Comparison.source p k n X₁ Y f₁ hp₁ U₁
local notation "a" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalCoefficientNaturality.sourceIso p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e
local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalCoefficientNaturality.restriction p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e

variable (g : ℕ) (b : Fin g → Γ(X₁.left, U₁.val)) (O : Y.left.Opens)
  (hO : ∀ i, (Supported.Comparison.opens p k n X₁ Y f₁ U₁).obj
    (Supported.Comparison.family p k n X₁ U₁ g b i) ≤ O)
  (hcover : (Supported.Comparison.opens p k n X₁ Y f₁ U₁).obj
    (⊤_ (PrincipalFrame.Index X₁.left U₁)) ⊓ O ≤
      ⨆ i, (Supported.Comparison.opens p k n X₁ Y f₁ U₁).obj
        (Supported.Comparison.family p k n X₁ U₁ g b i))
  (hglobal : (Supported.Comparison.opens p k n X₁ Y f₁ U₁).obj
    (⊤_ (PrincipalFrame.Index X₁.left U₁)) ⊔ O = ⊤)

local notation "rows" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SupportedRows.exactAt_succ p k n X₁ Y f₁ U₁ I g b

local notation "b₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SupportedReindexData.coefficients p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e g b
local notation "hO₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SupportedReindexGeometry.below p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e g b O hO
local notation "hcover₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SupportedReindexGeometry.cover p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e g b O hcover
local notation "hglobal₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SupportedReindexGeometry.global p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e O hglobal
local notation "rows₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SupportedRows.exactAt_succ p k n X₂ Y f₂ U₂ I g b₂

include hj in
theorem comparison :
    SupportedResidue.residue p k n X₁ Y f₁ hp₁ U₁ I g b O hO hcover rows hglobal =
      SupportedResidue.residue p k n X₂ Y f₂ hp₂ U₂ I g b₂ O hO₂ hcover₂ rows₂ hglobal₂ :=
  apply_composite
    (SupportedNaturality.comparison p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e I
      j hj g b O hO hcover hglobal (g+g))
    (ResidueTransport.residue_class p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e g b)

/-- At an actual section the support cover and all positive rows come
from the original geometry and the given generators of its ideal. -/
abbrev section_comparison
    (s₁ : Spec (CommRingCat.of (Truncated.Witt.Ring p k n)) ⟶ X₁.left)
    [IsClosedImmersion s₁]
    (hb : Ideal.span (Set.range b) = s₁.ker.ideal U₁)
    (hs : ⊤ ≤ s₁ ⁻¹ᵁ U₁.val) :=
  comparison p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e I j hj g b
    (SupportedSection.punctured p k n X₁ Y f₁ s₁)
    (SupportedSection.below p k n X₁ Y f₁ U₁ s₁ g b hb)
    (SupportedSection.cover p k n X₁ Y f₁ U₁ s₁ g b hb)
    (SupportedSection.global p k n X₁ Y f₁ U₁ s₁ hs)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SupportedResidueNaturality

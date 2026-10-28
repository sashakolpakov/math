import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ModelFrameSupportedComparison
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.Supported
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSupported.CechHomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SupportedRows

/-! # Supported Homotopy -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SupportedHomotopy

noncomputable section

/-! The local-frame homotopy preserves the actual supported
class in the original bounded crystalline cohomology. -/

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

def transportedMap :=
  ((a).hom ≫ ((H).mapHomologicalComplex (.up ℕ)).map
    (Principal.Comparison.map p k n X₂ Y f₂ hp₂ U₂ I)) ≫
      ((NatIso.mapHomologicalComplex
        (IncomingSectionReindex.sectionIso p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e)
        (.up ℕ)).app I.cocomplex).inv

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

abbrev otherSections := BoundedOpen.SectionSubsite.globalSections
  (p := p) (J := Ideal.span {(p : WittVector p k)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) w n
  (PrincipalSections.opens p k n X₂ Y f₂ U₂)

abbrev map_eq (i : ℕ) :=
  ModelFrameSupportedComparison.comparison
    p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e I j hj
    (ULift (Fin g)) (Supported.Comparison.family p k n X₁ U₁ g b)
    O hO hcover rows hglobal i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SupportedHomotopy

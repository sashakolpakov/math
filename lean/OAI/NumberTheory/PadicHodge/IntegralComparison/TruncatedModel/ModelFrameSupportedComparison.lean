import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FrameSupported
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalComparison
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.IncomingBaseHomotopy

/-! # Model Frame Supported Comparison -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ModelFrameSupportedComparison

noncomputable section

/-! The complete original principal comparison, with its genuine
factorizations and incoming homotopy, on every supported Čech family. -/

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
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y) n))
  (j : AlgebraicGeometry.Crystalline.Cohomology.Base.SmoothProperEtaleCover.BaseSmoothProperEtaleCover.Index (Truncated.Witt.Ring p k n) X₁)
  (hj : U₁.val ≤ AlgebraicGeometry.Crystalline.Cohomology.Base.ProperOrdinaryFormCharts.BaseSmoothProperOrdinaryFormCharts.opens (Truncated.Witt.Ring p k n) X₁ j)

abbrev comparison := FrameSupported.Resolution.comparison
  p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e I
  (PrincipalComparison.TypedMaps.incomingMap p k n X₁ Y f₁ hp₁ U₁ I)
  (PrincipalComparison.TypedMaps.comparisonMap p k n X₁ Y f₁ hp₁ U₁ I)
  (PrincipalComparison.TypedMaps.comparisonMap p k n X₂ Y f₂ hp₂ U₂ I)
  (PrincipalComparison.Identity.comparison p k n X₁ Y f₁ hp₁ U₁ I)
  (PrincipalComparison.Identity.comparison p k n X₂ Y f₂ hp₂ U₂ I)
  (IncomingBaseHomotopy.homotopy
    p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e I j hj)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ModelFrameSupportedComparison

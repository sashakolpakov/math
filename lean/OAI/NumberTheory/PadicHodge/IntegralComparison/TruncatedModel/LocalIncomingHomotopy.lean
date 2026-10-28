import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.IncomingFrame
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.BoundedFrameIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SmallFrameOpens
import OAI.NumberTheory.PadicHodge.IntegralComparison.CrystallinePrincipal.IsoOpens

/-! # Local Incoming Homotopy -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.LocalIncomingHomotopy

noncomputable section

/-! The original local injective comparisons for two isomorphic
native frames agree up to homotopy on one common incoming site. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev preimage {Y X : Scheme} (f : Y ⟶ X) (U : X.affineOpens) : Y.Opens := f ⁻¹ᵁ U.val

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
local notation "F₁" => Functor.obj (OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FrameFunctor.functor p k n X₁ Y f₁ hp₁) U₁
local notation "F₂" => Functor.obj (OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FrameFunctor.functor p k n X₂ Y f₂ hp₂) U₂
local notation "V₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.LocalIncomingHomotopy.preimage f₁ U₁
local notation "V₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.LocalIncomingHomotopy.preimage f₂ U₂

local instance globalSeparated : IsSeparated w := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance

include e in
omit [IsProper X₁.hom] [X₁.left.IsSeparated] [IsProper X₂.hom] [X₂.left.IsSeparated] [IsSeparated Y.hom] in
theorem opens_eq : V₁ = V₂ :=
  (SmallFrameOpens.opensRange p k n X₁ Y f₁ hp₁ U₁).symm.trans
    ((CrystallinePrincipal.IsoOpens.opens_eq p k Y e).symm.trans
      (SmallFrameOpens.opensRange p k n X₂ Y f₂ hp₂ U₂))

variable (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
  (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
  (Witt.Crystalline.wittStructureMap p k Y) n))

def frameMap := Incoming.FrameHomotopy.Comparison.map w n V₁ F₁ F₂
  (BoundedFrameIso.iso p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e).hom

def targetMap := Incoming.FrameTransport.Comparison.map w n V₁ V₂
  (opens_eq p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e) F₂ I
  (IncomingFrame.comparison p k n X₂ Y f₂ hp₂ U₂ I)

variable (i : AlgebraicGeometry.Crystalline.Cohomology.Base.SmoothProperEtaleCover.BaseSmoothProperEtaleCover.Index (Truncated.Witt.Ring p k n) X₁)
  (hi : U₁.val ≤ AlgebraicGeometry.Crystalline.Cohomology.Base.ProperOrdinaryFormCharts.BaseSmoothProperOrdinaryFormCharts.opens (Truncated.Witt.Ring p k n) X₁ i)

def homotopy : Homotopy (IncomingFrame.comparison p k n X₁ Y f₁ hp₁ U₁ I)
    (frameMap p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e ≫
      targetMap p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e I) := by
  let : QuasiIso (Incoming.FrameHomotopy.Comparison.augmentation w n V₁ F₁) :=
    IncomingFrame.quasiIso p k n X₁ Y f₁ hp₁ U₁ i hi
  exact Incoming.FrameTransport.Comparison.homotopy w n V₁ V₂
    (opens_eq p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e) F₁ I F₂
    (BoundedFrameIso.iso p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e).hom
    (IncomingFrame.comparison p k n X₁ Y f₁ hp₁ U₁ I)
    (IncomingFrame.comparison p k n X₂ Y f₂ hp₂ U₂ I)
    (IncomingFrame.augmentation p k n X₁ Y f₁ hp₁ U₁ I)
    (IncomingFrame.augmentation p k n X₂ Y f₂ hp₂ U₂ I)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.LocalIncomingHomotopy

import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FrameFunctor
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FrameClosed
import OAI.NumberTheory.PadicHodge.GeometricComparison.PrincipalFrameComplex

/-! # Principal Complex -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalComplex.Comparison

noncomputable section

/-! The actual finite-level model frame diagram has its natural
principal-base comparison to ordinary Witt-relative forms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))) [Smooth X.hom]
  (Y : Over (Spec (CommRingCat.of k))) (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))

local notation "W" => WittVector p k
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "N" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FrameFunctor.functor p k n X Y f hp

def frames := (N).op ⋙ (BoundedCrystalline.Site.inclusion w n).op

def rings : X.left.affineOpensᵒᵖ ⥤ CommAlgCat W :=
  (N).op ⋙ GeometricComparison.Crystalline.FrameRingFunctor.CrystallineFrameRingFunctor.bounded w n

def pdComplexes : X.left.affineOpensᵒᵖ ⥤ CochainComplex (ModuleCat W) ℕ :=
  (N).op ⋙ GeometricComparison.Crystalline.FrameComplexFunctor.CrystallineFrameComplexFunctor.bounded w n

def ordinaryComplexes : X.left.affineOpensᵒᵖ ⥤ CochainComplex (ModuleCat W) ℕ :=
  rings p k n X Y f hp ⋙ OrdinaryDeRhamFunctor.Ordinary.functor W

theorem ideal_generated (I : X.left.affineOpensᵒᵖ) :
    ((frames p k n X Y f hp).obj I).unop.ideal =
      Ideal.span {((frames p k n X Y f hp).obj I).unop.base (p : W)} := by
  exact (FrameClosed.ideal_generated p k n X Y f hp I.unop.val I.unop.property).trans
    (by rw [Ideal.map_span, Set.image_singleton]; rfl)

def iso : pdComplexes p k n X Y f hp ≅ ordinaryComplexes p k n X Y f hp :=
  GeometricComparison.PrincipalFrameComplex.PrincipalFrameComplexComparison.iso (p : W) γ w (frames p k n X Y f hp)
    (ideal_generated p k n X Y f hp)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalComplex.Comparison

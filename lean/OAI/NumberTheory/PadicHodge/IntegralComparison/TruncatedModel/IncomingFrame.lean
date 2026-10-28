import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.Incoming
import OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.FrameTransport

/-! # Incoming Frame -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.IncomingFrame

noncomputable section

/-! The native chart comparison is the augmentation-preserving
comparison of its original bounded crystalline frame. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (U : X.left.affineOpens)
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y) n))

local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y
local notation "F" => Functor.obj (OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FrameFunctor.functor p k n X Y f hp) U
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.IncomingRestriction.restriction p k n X Y f U

local instance globalSeparated : IsSeparated w := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance

def comparison : Incoming.FrameHomotopy.Comparison.complex w n (f ⁻¹ᵁ U.val) F ⟶
    (ExactInjectiveResolution.map R I).cocomplex :=
  Incoming.Comparison.map p k n X Y f hp U I

theorem augmentation : Incoming.FrameHomotopy.Comparison.augmentation w n (f ⁻¹ᵁ U.val) F ≫
    comparison p k n X Y f hp U I = (ExactInjectiveResolution.map R I).ι :=
  Incoming.Comparison.augmentation_map p k n X Y f hp U I

variable (i : AlgebraicGeometry.Crystalline.Cohomology.Base.SmoothProperEtaleCover.BaseSmoothProperEtaleCover.Index (Truncated.Witt.Ring p k n) X)
  (hi : U.val ≤ AlgebraicGeometry.Crystalline.Cohomology.Base.ProperOrdinaryFormCharts.BaseSmoothProperOrdinaryFormCharts.opens (Truncated.Witt.Ring p k n) X i)

include hi in
theorem quasiIso : QuasiIso (Incoming.FrameHomotopy.Comparison.augmentation w n (f ⁻¹ᵁ U.val) F) :=
  Incoming.Comparison.augmentation_quasiIso p k n X Y f hp U i hi

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.IncomingFrame

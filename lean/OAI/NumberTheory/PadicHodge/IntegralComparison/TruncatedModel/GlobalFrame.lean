import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.GlobalEdge

/-! # Global Frame -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.GlobalFrame.Comparison

noncomputable section

/-! The actual model frame de Rham Cech total computes the original global bounded crystalline cohomology in every degree. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))

local notation "Rcoeff" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)
local notation "U" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechSliceResolution.opens p k n X
local notation "N" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve U
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y

variable (J : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
  (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
  (Witt.Crystalline.wittStructureMap p k Y) n))

def complex : CochainComplex (ModuleCat.{2} Rcoeff) ℕ :=
  FrameCech.Complexes.source p k n X Y f hp

def homologyIso (i : ℕ) :
    (FrameCech.Complexes.source p k n X Y f hp).homology i ≅
    ModuleCat.of Rcoeff (BoundedCrystalline.CrystallineCohomology.Cohomology (p := p)
      (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) w n i) := by
  let := FrameCech.Comparison.quasiIso p k n X Y f hp J
  exact isoOfQuasiIsoAt (FrameCech.Comparison.map p k n X Y f hp J) i ≪≫
    GlobalEdge.InjectiveCech.homologyIso p k n X Y f J i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.GlobalFrame.Comparison

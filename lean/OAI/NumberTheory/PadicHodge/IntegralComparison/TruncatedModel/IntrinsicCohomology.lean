import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.GlobalDeRham
import OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.CoefficientCoordinates

/-! # Intrinsic Cohomology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.IntrinsicCohomology.Intrinsic

noncomputable section

/-! The finite-level comparison on the native underlying additive
cohomology groups, with the coefficient enlargements removed explicitly. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))

local notation "W" => WittVector p k
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.Witt.Ring p k n
local notation "U" => ModuleCat.restrictScalars (algebraMap W S)
local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.total S X
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y

variable (J : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
  (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
  (Witt.Crystalline.wittStructureMap p k Y) n))

def comparisonEquiv (i : ℕ) : (K).homology i ≃+
    BoundedCrystalline.CrystallineCohomology.Cohomology (p := p)
      (J := Ideal.span {(p : W)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) w n i :=
  (AlgebraicGeometry.Crystalline.Cohomology.Mapped.ComplexHomology.MappedComplexHomology.iso U K i).toLinearEquiv.toAddEquiv.symm.trans
    ((Witt.CoefficientCoordinates.cohomologyEquiv p k
      (GlobalDeRham.Comparison.rawComplex p k n X) i).symm.trans
      (GlobalDeRham.Comparison.homologyIso p k n X Y f hp J i).toLinearEquiv.toAddEquiv)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.IntrinsicCohomology.Intrinsic

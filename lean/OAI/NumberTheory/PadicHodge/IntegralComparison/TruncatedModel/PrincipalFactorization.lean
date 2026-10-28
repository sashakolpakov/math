import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.Incoming
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalDiagramFactorization

/-! # Principal Factorization -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFactorization

noncomputable section

/-! The original global diagonal comparison on principal opens
factors through the native local comparison on the fixed incoming subsite. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (V : X.left.affineOpens)

local notation "W" => WittVector p k
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := W)
local notation "U" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechSliceResolution.opens p k n X
local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ResolutionDiagram.diagram p k n X Y f hp
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SectionBifunctor.sections p k n X Y f
local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.Principal.Comparison.restriction p k n X V
local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.IncomingRestriction.restriction p k n X Y f V
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalSections.localSections p k n X Y f V
local notation "e" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalSections.iso p k n X Y f V
local notation "hF" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.IncomingRestriction.meet_isIso p k n X Y f hp V
local notation "hS" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SectionRowRestriction.meet_isIso p k n X Y f hp
local notation "M" => OAI.NumberTheory.PadicHodge.GeometricComparison.Section.DiagonalCone.SectionDiagonalCone.source X.left.affineOpens S P
local notation "η" => OAI.NumberTheory.PadicHodge.GeometricComparison.Section.DiagonalCone.SectionDiagonalCone.cone X.left.affineOpens S P hS

local instance globalSeparated : IsSeparated w := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance
local instance globalCoproducts : HasCoproducts.{0}
    (BoundedCrystalline.Site.ModuleSheaf (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n) :=
  GeometricComparison.Module.SheafCoproducts.ModuleSheafCoproducts.hasCoproducts R (BoundedCrystalline.Site.topology w n)
local instance localCoproducts : HasCoproducts.{0}
    (BoundedOpen.Subsite.ModuleSheaf (p := p) (J := Ideal.span {(p : W)}) (δ := γ)
      w (f ⁻¹ᵁ V.val).ι n) :=
  GeometricComparison.Module.SheafCoproducts.ModuleSheafCoproducts.hasCoproducts R (BoundedOpen.Subsite.topology w (f ⁻¹ᵁ V.val).ι n)

variable (J : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
  (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
  (Witt.Crystalline.wittStructureMap p k Y) n))

abbrev native_factorization := PrincipalDiagramFactorization.comparison
  p k n X Y f V P hF M η
  (DiagonalCech.Comparison.totalIso p k n X Y f hp)
  (CechInjective.Comparison.map p k n X Y f hp J)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFactorization

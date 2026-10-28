import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalIncomingComponents

/-! # Principal Incoming Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalIncomingMap

noncomputable section

/-! The original principal comparison factors through the checked
local incoming-frame comparison. -/

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
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := W)
local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ResolutionDiagram.diagram p k n X Y f hp
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SectionBifunctor.sections p k n X Y f
local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.Principal.Comparison.restriction p k n X V
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalSections.localSections p k n X Y f V
local notation "e" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalSections.iso p k n X Y f V
local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Diagram.functor X.left V.val V.property

variable (J : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
  (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
  (Witt.Crystalline.wittStructureMap p k Y) n))

attribute [local instance] PrincipalIncomingBase.Map.globalSeparated PrincipalIncomingBase.Map.globalCoproducts PrincipalIncomingBase.Map.localCoproducts

abbrev factorization := HomologicalComplex.hom_ext
  (Principal.Comparison.map p k n X Y f hp V J ≫
    ((NatIso.mapHomologicalComplex e (.up ℕ)).app J.cocomplex).hom)
  (PrincipalIncomingBase.Map.viaIncoming p k n X Y f hp V J)
  (fun q => NatTrans.ext (funext (fun r => PrincipalIncomingComponents.Map.factorization_component p k n X Y f hp V J q r)))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalIncomingMap

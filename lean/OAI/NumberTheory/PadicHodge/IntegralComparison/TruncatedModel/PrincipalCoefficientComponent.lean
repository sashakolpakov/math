import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.Principal
import OAI.NumberTheory.PadicHodge.IntegralComparison.Open.CrystallinePDComponent

/-! # Principal Coefficient Component -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalCoefficientComponent.PD

/-! Exact components of the original principal PD comparison. This
normalizes assembly and native algebra coordinates once. -/
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
local notation "C" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFrame.Index X.left U
local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Diagram.functor X.left U.val U.property

def coordinate (r : C) := (Small.PDIntrinsicCoordinates.Intrinsic.iso p k Y).hom.app
  (op ((SmallFrame.smallFunctor p k n X Y f hp).obj ((P).obj r)))

omit [IsProper X.hom] [X.left.IsSeparated] [IsSeparated Y.hom] in
theorem sourceIso_component (q : ℕ) (r : C) :
    ((PrincipalFrame.sourceIso p k n X Y f hp U).hom.f q).app (op r) = 𝟙 _ := by
  change (𝟙 _ ≫ 𝟙 _) = 𝟙 _
  exact Category.id_comp _

omit [IsProper X.hom] [X.left.IsSeparated] [IsSeparated Y.hom] in
theorem nativePDMap_component (q : ℕ) (r : C) :
    ((Principal.Comparison.nativePDMap p k n X Y f hp U).f q).app (op r) =
      ((Small.PDComplexCoordinates.originalFunctor p k Y).map
        (PrincipalFrame.map p k n X Y f hp U r).op).f q ≫
          (coordinate p k n X Y f hp U r).f q := by
  have hc := congrArg (fun a => a.f q) (Open.CrystallinePDComponent.hom_app p k Y
    (SmallFrame.bigFunctor p k n X Y f hp)
    (SmallFrame.mapToX_open p k n X Y f hp) ((P).obj r))
  change (((PrincipalFrame.sourceIso p k n X Y f hp U).hom.f q).app (op r) ≫
    ((Small.PDComplexCoordinates.originalFunctor p k Y).map
      (PrincipalFrame.map p k n X Y f hp U r).op).f q) ≫ _ = _
  rw [sourceIso_component, Category.id_comp]
  exact congrArg (fun z => ((Small.PDComplexCoordinates.originalFunctor p k Y).map
    (PrincipalFrame.map p k n X Y f hp U r).op).f q ≫ z) hc

end NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalCoefficientComponent.PD

namespace NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalCoefficientComponent

/-! Coefficient change in the native principal comparison is the
literal double-lift functor on each PD component. -/
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

omit [IsProper X.hom] [X.left.IsSeparated] [IsSeparated Y.hom] in
theorem component (q : ℕ) (r : PrincipalFrame.Index X.left U) :
    ((Principal.Comparison.coefficientMap p k n X Y f hp U).f q).app (op r) =
    (Principal.Comparison.coefficients p k).map
      (((Principal.Comparison.nativePDMap p k n X Y f hp U).f q).app (op r)) := by
  change (Principal.Comparison.coefficients p k).map _ ≫ 𝟙 _ = _
  exact Category.comp_id _

end NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalCoefficientComponent

end

end OAI

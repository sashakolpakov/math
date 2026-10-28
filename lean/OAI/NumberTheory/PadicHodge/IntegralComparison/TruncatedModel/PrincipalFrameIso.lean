import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFrameSections
import OAI.NumberTheory.PadicHodge.GeometricComparison.FixedDiagramInverse

/-! # Principal Frame Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFrameIso

noncomputable section

/-! The original principal section diagonal is canonically isomorphic
to the sections of the fixed relative frame resolution. -/

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

local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Diagram.functor X.left U.val U.property
local notation "P₀" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ResolutionDiagram.diagram p k n X Y f hp
local notation "S₀" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SectionBifunctor.sections p k n X Y f
local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.Principal.Comparison.restriction p k n X U
local notation "S" => S₀ ⋙ H
local notation "P" => Functor.op F ⋙ P₀
local notation "K" => Functor.obj P₀ (op U)
local notation "η" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFrameSections.cone p k n X Y f hp U
local notation "h₀" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SectionRowRestriction.meet_isIso p k n X Y f hp

omit [IsProper X.hom] in
theorem fixed_isIso : IsIso (GeometricComparison.FixedDiagramTransformation.FixedDiagramSections.map S K P η) :=
  GeometricComparison.FixedDiagramInverse.FixedDiagramSectionIso.isIso S K P η (fun r =>
    GeometricComparison.Semilattice.LocalConeUpper.SemilatticeLocalConeUpper.restriction_isIso X.left.affineOpens ((F).obj r.unop)
      ((GeometricComparison.Section.ComplexBifunctor.SectionComplexBifunctor.functor S₀ P₀).obj (op ((F).obj r.unop)))
      (h₀ ((F).obj r.unop)) U
      (leOfHom (AffinePrincipal.Diagram.projection X.left U.val U.property r.unop)))

instance map_isIso : IsIso (PrincipalFrameSections.map p k n X Y f hp U) := by
  let := fixed_isIso p k n X Y f hp U
  dsimp only [PrincipalFrameSections.map]
  infer_instance

omit [IsProper X.hom] in
theorem inverse_eq_inv : PrincipalFrameSections.inverse p k n X Y f hp U =
    inv (PrincipalFrameSections.map p k n X Y f hp U) := by
  apply (cancel_mono (PrincipalFrameSections.map p k n X Y f hp U)).1
  rw [PrincipalFrameSections.inverse_map, IsIso.inv_hom_id]

omit [IsProper X.hom] in
theorem map_inverse : PrincipalFrameSections.map p k n X Y f hp U ≫
    PrincipalFrameSections.inverse p k n X Y f hp U = 𝟙 _ := by
  rw [inverse_eq_inv, IsIso.hom_inv_id]

def iso : ((S).mapHomologicalComplex (.up ℕ)).obj K ≅
    ((H).mapHomologicalComplex (.up ℕ)).obj (GeometricComparison.Section.DiagonalCone.SectionDiagonalCone.source X.left.affineOpens S₀ P₀) where
  hom := PrincipalFrameSections.map p k n X Y f hp U
  inv := PrincipalFrameSections.inverse p k n X Y f hp U
  hom_inv_id := map_inverse p k n X Y f hp U
  inv_hom_id := PrincipalFrameSections.inverse_map p k n X Y f hp U

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFrameIso

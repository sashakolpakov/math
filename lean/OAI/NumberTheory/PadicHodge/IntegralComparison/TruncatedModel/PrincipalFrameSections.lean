import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalSections
import OAI.NumberTheory.PadicHodge.GeometricComparison.FixedDiagramTransformation
import OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.LocalConeUpper

/-! # Principal Frame Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFrameSections

noncomputable section

/-! On the principal subopens of one model chart, the original
diagonal section complex is identified with sections of its fixed
relative crystalline frame resolution. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

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
local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Diagram.functor X.left U.val U.property
local notation "P₀" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ResolutionDiagram.diagram p k n X Y f hp
local notation "S₀" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SectionBifunctor.sections p k n X Y f
local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.Principal.Comparison.restriction p k n X U
local notation "S" => S₀ ⋙ H
local notation "P" => Functor.op F ⋙ P₀
local notation "K" => Functor.obj P₀ (op U)
local notation "h₀" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SectionRowRestriction.meet_isIso p k n X Y f hp

def cone : (Functor.const Cᵒᵖ).obj K ⟶ P where
  app r := (P₀).map (AffinePrincipal.Diagram.projection X.left U.val U.property r.unop).op
  naturality r s a := by
    change 𝟙 _ ≫ (P₀).map (AffinePrincipal.Diagram.projection X.left U.val U.property s.unop).op =
      (P₀).map (AffinePrincipal.Diagram.projection X.left U.val U.property r.unop).op ≫
        (P₀).map ((F).map a.unop).op
    rw [Category.id_comp, ← CategoryTheory.Functor.map_comp]
    exact congrArg (P₀).map
      (congrArg Quiver.Hom.op (AffinePrincipal.Diagram.projection_natural
        X.left U.val U.property a.unop)).symm

def targetIso : AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (GeometricComparison.FixedDiagramTransformation.FixedDiagramSections.target S P) ≅
    ((H).mapHomologicalComplex (.up ℕ)).obj (GeometricComparison.Section.DiagonalCone.SectionDiagonalCone.source X.left.affineOpens S₀ P₀) :=
  Iso.refl _

def map : ((S).mapHomologicalComplex (.up ℕ)).obj K ⟶
    ((H).mapHomologicalComplex (.up ℕ)).obj (GeometricComparison.Section.DiagonalCone.SectionDiagonalCone.source X.left.affineOpens S₀ P₀) :=
  GeometricComparison.FixedDiagramTransformation.FixedDiagramSections.map S K P (cone p k n X Y f hp U) ≫ (targetIso p k n X Y f hp U).hom

def inverse : ((H).mapHomologicalComplex (.up ℕ)).obj (GeometricComparison.Section.DiagonalCone.SectionDiagonalCone.source X.left.affineOpens S₀ P₀) ⟶
    ((S).mapHomologicalComplex (.up ℕ)).obj K :=
  ((H).mapHomologicalComplex (.up ℕ)).map ((GeometricComparison.Section.DiagonalCone.SectionDiagonalCone.cone X.left.affineOpens S₀ P₀ h₀).app (op U))

omit [IsProper X.hom] in
theorem inverse_map : inverse p k n X Y f hp U ≫ PrincipalFrameSections.map p k n X Y f hp U = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply NatTrans.ext
  funext r
  change ((((GeometricComparison.Section.DiagonalCone.SectionDiagonalCone.cone X.left.affineOpens S₀ P₀ h₀).app (op U)).f q).app
    (op ((F).obj r.unop))) ≫
      (((GeometricComparison.FixedDiagramTransformation.FixedDiagramSections.map S K P (cone p k n X Y f hp U)).f q).app r ≫ 𝟙 _) = 𝟙 _
  rw [Category.comp_id, GeometricComparison.FixedDiagramTransformation.FixedDiagramSections.component, GeometricComparison.Section.DiagonalCone.SectionDiagonalCone.cone_app_f]
  exact congrArg (fun a => a.f q) (GeometricComparison.Semilattice.LocalConeUpper.SemilatticeLocalConeUpper.app_restriction
    X.left.affineOpens ((F).obj r.unop)
    ((GeometricComparison.Section.ComplexBifunctor.SectionComplexBifunctor.functor S₀ P₀).obj (op ((F).obj r.unop)))
    (h₀ ((F).obj r.unop)) U
    (leOfHom (AffinePrincipal.Diagram.projection X.left U.val U.property r.unop)))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFrameSections

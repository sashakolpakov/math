import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.LocalMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.SectionReindexCoordinates

/-! # Local Reindex Steps -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.LocalReindexSteps

noncomputable section

/-! The local bounded-frame map commutes with reindexing and with
the canonical identification of equal families of geometric opens. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w v' w'
variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of B)) [IsSeparated f] (n : ℕ)
  {C : Type v} [Category.{w} C] {D : Type v'} [Category.{w'} D]
  (r : D ⥤ C) (O : C ⥤ Y.Opensᵒᵖ)
  (G : C ⥤ (BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)ᵒᵖ)
  (F : (BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)ᵒᵖ)
  (ρ : (Functor.const C).obj F ⟶ G)
  [IsIso (LocalMap.restriction f n O G F ρ)]

local notation "Q" => OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.ResolutionFunctor.BoundedFrameResolutionFunctor.sheafFunctor (p := p) (J := J) (δ := δ) f n
local notation "ρ'" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.SectionReindex.cone f n r G F ρ
abbrev restriction :
    (C ⥤ ModuleCat.{u + 2} (Crystalline.ExactRestriction.Coeff (B := B))) ⥤
      (D ⥤ ModuleCat.{u + 2} (Crystalline.ExactRestriction.Coeff (B := B))) :=
  GeometricComparison.FixedFrameEq.FixedFrameSectionReindex.restriction r

local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.LocalReindexSteps.restriction (B := B) r

local instance pulled_isIso : IsIso
    (LocalMap.restriction f n (r ⋙ O) (r ⋙ G) F ρ') :=
  SectionReindex.fixed_isIso f n r O G F ρ

abbrev diagonal := GeometricComparison.FixedFrameDiagonalNaturality.FixedFrameSectionNaturality.diagonal
  (FamilySections.Family.sections f n O)
  (FamilySections.Family.source f n G)
  (FamilySections.Family.diagram f n G)
  (FamilySections.Family.openTransformation f n O G)

omit [IsIso (LocalMap.restriction f n O G F ρ)] in
theorem restriction_component (q : ℕ) (d : D) :
    ((LocalMap.restriction f n O G F ρ).f q).app (r.obj d) =
      ((LocalMap.restriction f n (r ⋙ O) (r ⋙ G) F ρ').f q).app d := by
  rw [GeometricComparison.FixedDiagramTransformation.FixedDiagramSections.component, GeometricComparison.FixedDiagramTransformation.FixedDiagramSections.component,
    SectionReindexCoordinates.cone_app,
    SectionReindexCoordinates.section_map]

omit [IsIso (LocalMap.restriction f n O G F ρ)] in
abbrev restriction_eq :=
  GeometricComparison.FixedFrameEq.FixedFrameSectionReindex.map_eq r (FamilySections.Family.sections f n O)
    ((Q).obj F) (FamilySections.Family.diagram f n G)
    (FamilySections.Family.cone f n F ρ)

/-- Reindex the diagonal in the same source and target complexes as the new family. -/
def reindexedDiagonal :
    AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (FamilySections.Family.source f n (r ⋙ G)) ⟶
      AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ)
        (GeometricComparison.FixedDiagramTransformation.FixedDiagramSections.target (FamilySections.Family.sections f n (r ⋙ O))
          (FamilySections.Family.diagram f n (r ⋙ G))) :=
  ((H).mapHomologicalComplex (.up ℕ)).map (diagonal f n O G)

theorem diagonal_eq : reindexedDiagonal f n r O G =
    diagonal f n (r ⋙ O) (r ⋙ G) := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply NatTrans.ext
  funext d
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.LocalReindexSteps

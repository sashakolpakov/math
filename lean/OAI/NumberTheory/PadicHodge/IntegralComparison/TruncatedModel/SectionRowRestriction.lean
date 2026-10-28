import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedTruncated.FrameProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SectionBifunctor
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechGeometricTotal
import OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.ChartSectionFunctorIso

/-! # Section Row Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SectionRowRestriction

noncomputable section

/-! The original Zariski section rows have invertible meet restrictions,
via the actual geometric chart and original sheafification comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (I : X.left.affineOpens)

local notation "W" => WittVector p k
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "C" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.AffineModelFrame.targetRing p k n X Y f I.val
local instance specialAlgebra : Algebra k C := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra k Y (f ⁻¹ᵁ I.val)
local notation "wI" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k (OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation.affineScheme k C)
local notation "g" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.AffineModelFrame.chart p k n X Y f hp I.val I.property
local notation "hg" => (OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.OpenPresentation.overWitt p k C Y (OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.AffineModelFrame.chart p k n X Y f hp I.val I.property) (OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.AffineModelFrame.chart_over p k n X Y f hp I.val I.property))
local notation "U" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechSliceResolution.opens p k n X
local notation "Pgeo" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.GeometricSliceDiagram.diagram p k n X Y f hp I

local instance localSeparated : IsSeparated wI := BoundedTruncated.FrameProduct.structureMap_separated p k C
local instance globalSeparated : IsSeparated w := by dsimp only [Witt.Crystalline.wittStructureMap]; infer_instance
local instance chartOpen : IsOpenImmersion g := Truncated.AffineModelFrame.chart_open p k n X Y f hp I.val I.property

local notation "L" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechGeometricTotal.localSheafification p k n X Y f I
local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.GeometricSliceDiagram.meet_isIso p k n X Y f hp I

local notation "Ppre" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechPresheaf.diagram p k n X Y f hp
local notation "Psh" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ResolutionDiagram.diagram p k n X Y f hp
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechGeometricTotal.restriction p k n X Y f hp I
local notation "Rcoeff" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)
abbrev localSections := Sheaf.PresheafSectionComplex.sectionFunctor.{1, 0, 1, 2}
  Rcoeff (BoundedCrystalline.Site.topology (p := p) (J := Ideal.span {(p : W)}) (δ := γ) wI n)

theorem restricted_meet_isIso (V : X.left.affineOpens) : IsIso
    (((R).mapHomologicalComplex (.up ℕ)).map
      ((Psh).map (homOfLE (inf_le_left : V ⊓ I ≤ V)).op)) := by
  let : IsIso ((Pgeo).map (homOfLE (inf_le_left : V ⊓ I ≤ V)).op) :=
    GeometricSliceDiagram.meet_isIso p k n X Y f hp I V
  have hm : IsIso (((L).mapHomologicalComplex (.up ℕ)).map
      ((Pgeo).map (homOfLE (inf_le_left : V ⊓ I ≤ V)).op)) := inferInstance
  exact (NatIso.isIso_map_iff
    (NatIso.mapHomologicalComplex (BoundedFrame.SheafRestriction.sheafificationIso g hg n) (.up ℕ))
    ((Ppre).map (homOfLE (inf_le_left : V ⊓ I ≤ V)).op)).mpr hm

theorem sections_meet_isIso (V : X.left.affineOpens) : IsIso
    (((BoundedOpen.SectionComplex.functor (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n ⋙
      BoundedOpen.SectionComplex.evaluation (B := W) (f ⁻¹ᵁ I.val)).mapHomologicalComplex (.up ℕ)).map
        ((Psh).map (homOfLE (inf_le_left : V ⊓ I ≤ V)).op)) := by
  let := restricted_meet_isIso p k n X Y f hp I V
  have hm : IsIso (((localSections p k n X Y f I).mapHomologicalComplex (.up ℕ)).map
      (((R).mapHomologicalComplex (.up ℕ)).map
        ((Psh).map (homOfLE (inf_le_left : V ⊓ I ≤ V)).op))) := inferInstance
  have h := (NatIso.isIso_map_iff
    (NatIso.mapHomologicalComplex (GeometricComparison.Bounded.ChartSectionFunctorIso.BoundedChartSectionFunctorIso.iso g hg n) (.up ℕ))
    ((Psh).map (homOfLE (inf_le_left : V ⊓ I ≤ V)).op)).mp hm
  have hj : (g).opensRange = f ⁻¹ᵁ I.val :=
    IsAffineOpen.opensRange_fromSpec (Truncated.AffineModelFrame.residue_affine p k n X Y f hp I.val I.property)
  erw [hj] at h
  exact h

theorem meet_isIso (V : X.left.affineOpens) : IsIso
    (((SectionBifunctor.rows p k n X Y f hp).obj (op I)).map
      (homOfLE (inf_le_left : V ⊓ I ≤ V)).op) :=
  (NatIso.isIso_map_iff (SectionBifunctor.rowIso p k n X Y f hp I)
    (homOfLE (inf_le_left : V ⊓ I ≤ V)).op).mpr
      (sections_meet_isIso p k n X Y f hp I V)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SectionRowRestriction

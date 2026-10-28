import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionBifunctor
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechTotal
import OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.ChartSectionFunctorIso
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ChartImage

/-! # Section Row Restriction -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionRowRestriction.IntrinsicPadicSectionRowRestriction

noncomputable section

/-! The original Zariski section rows have invertible meet restrictions,
via the actual geometric chart and original sheafification comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (n : ℕ) (I : X.left.affineOpens)

local notation "W" => WittVector p (ZMod p)
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)
local notation "C" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.AffineFrame.IntrinsicPadicAffineFrame.targetRing p X Y f I.val
local instance specialAlgebra : Algebra (ZMod p) C := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra (ZMod p) Y (f ⁻¹ᵁ I.val)
local notation "wI" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) (OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation.affineScheme (ZMod p) C)
local notation "g" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ChartImage.IntrinsicPadicOpenFrame.chart p X Y f hp I.val I.property
local notation "hg" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ChartImage.IntrinsicPadicOpenFrame.chart_over_witt p X Y f hp I.val I.property
local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X
local notation "Pgeo" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SliceDiagram.IntrinsicPadicGeometricSliceDiagram.diagram p X Y f hp n I

local instance localSeparated : IsSeparated wI := IntegralComparison.BoundedSmooth.WittFrameProduct.structureMap_separated p (ZMod p) C
local instance globalSeparated : IsSeparated w := by dsimp only [IntegralComparison.Witt.Crystalline.wittStructureMap]; infer_instance
local instance chartOpen : IsOpenImmersion g := ChartImage.IntrinsicPadicOpenFrame.chart_open p X Y f hp I.val I.property

local notation "L" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechTotal.IntrinsicPadicCechGeometricTotal.localSheafification p X Y f n I
local notation "H" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SliceDiagram.IntrinsicPadicGeometricSliceDiagram.meet_isIso p X Y f hp n I

local notation "Ppre" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechPresheafResolution.IntrinsicPadicCechPresheafResolution.diagram p X Y f hp n
local notation "Psh" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PadicResolutionDiagram.IntrinsicPadicResolutionDiagram.diagram p X Y f hp n
local notation "R" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechTotal.IntrinsicPadicCechGeometricTotal.restriction p X Y f hp n I
local notation "Rcoeff" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
abbrev localSections := IntegralComparison.Sheaf.PresheafSectionComplex.sectionFunctor.{1, 0, 1, 2}
  Rcoeff (IntegralComparison.BoundedCrystalline.Site.topology (p := p) (J := Ideal.span {(p : W)}) (δ := γ) wI n)

theorem restricted_meet_isIso (V : X.left.affineOpens) : IsIso
    (((R).mapHomologicalComplex (.up ℕ)).map
      ((Psh).map (homOfLE (inf_le_left : V ⊓ I ≤ V)).op)) := by
  let : IsIso ((Pgeo).map (homOfLE (inf_le_left : V ⊓ I ≤ V)).op) :=
    SliceDiagram.IntrinsicPadicGeometricSliceDiagram.meet_isIso p X Y f hp n I V
  have hm : IsIso (((L).mapHomologicalComplex (.up ℕ)).map
      ((Pgeo).map (homOfLE (inf_le_left : V ⊓ I ≤ V)).op)) := inferInstance
  exact (NatIso.isIso_map_iff
    (NatIso.mapHomologicalComplex (IntegralComparison.BoundedFrame.SheafRestriction.sheafificationIso g hg n) (.up ℕ))
    ((Ppre).map (homOfLE (inf_le_left : V ⊓ I ≤ V)).op)).mpr hm

theorem sections_meet_isIso (V : X.left.affineOpens) : IsIso
    (((IntegralComparison.BoundedOpen.SectionComplex.functor (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n ⋙
      IntegralComparison.BoundedOpen.SectionComplex.evaluation (B := W) (f ⁻¹ᵁ I.val)).mapHomologicalComplex (.up ℕ)).map
        ((Psh).map (homOfLE (inf_le_left : V ⊓ I ≤ V)).op)) := by
  let := restricted_meet_isIso p X Y f hp n I V
  have hm : IsIso (((localSections p X Y f n I).mapHomologicalComplex (.up ℕ)).map
      (((R).mapHomologicalComplex (.up ℕ)).map
        ((Psh).map (homOfLE (inf_le_left : V ⊓ I ≤ V)).op))) := inferInstance
  have h := (NatIso.isIso_map_iff
    (NatIso.mapHomologicalComplex (Bounded.ChartSectionFunctorIso.BoundedChartSectionFunctorIso.iso g hg n) (.up ℕ))
    ((Psh).map (homOfLE (inf_le_left : V ⊓ I ≤ V)).op)).mp hm
  erw [ChartImage.IntrinsicPadicChartImage.opensRange] at h
  exact h

theorem meet_isIso (V : X.left.affineOpens) : IsIso
    (((SectionBifunctor.IntrinsicPadicSectionBifunctor.rows p X Y f hp n).obj (op I)).map
      (homOfLE (inf_le_left : V ⊓ I ≤ V)).op) :=
  (NatIso.isIso_map_iff (SectionBifunctor.IntrinsicPadicSectionBifunctor.rowIso p X Y f hp n I)
    (homOfLE (inf_le_left : V ⊓ I ≤ V)).op).mpr
      (sections_meet_isIso p X Y f hp n I V)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionRowRestriction.IntrinsicPadicSectionRowRestriction

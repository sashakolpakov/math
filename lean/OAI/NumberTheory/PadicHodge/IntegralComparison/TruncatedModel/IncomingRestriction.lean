import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SectionRowRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SubchartResolution
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.ImageRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.SheafAugmentation
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.RestrictionCongr

/-! # Incoming Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.IncomingRestriction

noncomputable section

/-! The native local frame resolves the original structure sheaf
on the fixed incoming subsite of its special-fiber open. -/

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
local notation "C" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.AffineModelFrame.targetRing p k n X Y f V.val
local instance specialAlgebra : Algebra k C := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra k Y (f ⁻¹ᵁ V.val)
local notation "wV" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k (OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation.affineScheme k C)
local notation "g" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.AffineModelFrame.chart p k n X Y f hp V.val V.property
local notation "hg" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.OpenPresentation.overWitt p k C Y
  (Truncated.AffineModelFrame.chart p k n X Y f hp V.val V.property)
  (Truncated.AffineModelFrame.chart_over p k n X Y f hp V.val V.property)
local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ResolutionDiagram.diagram p k n X Y f hp
local notation "η" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ResolutionDiagram.augmentation p k n X Y f hp
local notation "FG" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.AffineModelFrame.frame p k n X Y f hp V.val V.property
local notation "FL" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.AffineModelFrame.localFrame p k n X Y f hp V.val V.property

local instance localSeparated : IsSeparated wV := BoundedTruncated.FrameProduct.structureMap_separated p k C
local instance globalSeparated : IsSeparated w := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance
local instance chartOpen : IsOpenImmersion g :=
  Truncated.AffineModelFrame.chart_open p k n X Y f hp V.val V.property

abbrev restriction := BoundedOpen.Subsite.restriction (p := p)
  (J := Ideal.span {(p : W)}) (δ := γ) w (f ⁻¹ᵁ V.val).ι n

omit [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated] [IsSeparated Y.hom] in
theorem chart_range : (g).opensRange = f ⁻¹ᵁ V.val :=
  IsAffineOpen.opensRange_fromSpec
    (Truncated.AffineModelFrame.residue_affine p k n X Y f hp V.val V.property)

omit [IsProper X.hom] in
theorem meet_isIso (T : X.left.affineOpens) : IsIso
    (((restriction p k n X Y f V).mapHomologicalComplex (.up ℕ)).map
      ((P).map (homOfLE (inf_le_left : T ⊓ V ≤ T)).op)) := by
  have h := BoundedOpen.ImageRestriction.isIso g hg n
    ((P).map (homOfLE (inf_le_left : T ⊓ V ≤ T)).op)
    (SectionRowRestriction.restricted_meet_isIso p k n X Y f hp V T)
  exact BoundedOpen.RestrictionCongr.isIso w n _ _ _ (chart_range p k n X Y f hp V) h

variable (i : AlgebraicGeometry.Crystalline.Cohomology.Base.SmoothProperEtaleCover.BaseSmoothProperEtaleCover.Index (Truncated.Witt.Ring p k n) X)
  (hi : V.val ≤ AlgebraicGeometry.Crystalline.Cohomology.Base.ProperOrdinaryFormCharts.BaseSmoothProperOrdinaryFormCharts.opens (Truncated.Witt.Ring p k n) X i)

include hi in
omit [X.left.IsSeparated] in
theorem augmentation_quasiIso : QuasiIso
    (((restriction p k n X Y f V).mapHomologicalComplex (.up ℕ)).map ((η).app (op V))) := by
  have hlocal := SubchartResolution.augmentation_quasiIso p k n X Y f hp V i hi
  let e := BoundedFrame.SheafRestriction.complexIso g hg n FL
  have hpull : QuasiIso (BoundedFrame.PullbackAugmentation.augmentation g hg n FG) := by
    apply (quasiIso_iff_comp_right _ e.hom).mp
    exact (BoundedFrame.SheafAugmentation.augmentation g hg n FL).symm ▸ hlocal
  have hraw : QuasiIso
      (((CechGeometricTotal.restriction p k n X Y f hp V).mapHomologicalComplex
        (.up ℕ)).map ((η).app (op V))) :=
    (quasiIso_iff_comp_left (BoundedFrame.PullbackAugmentation.sourceIso g hg n).inv _).mp hpull
  have h := BoundedOpen.ImageRestriction.quasiIso g hg n ((η).app (op V)) hraw
  exact BoundedOpen.RestrictionCongr.quasiIso w n _ _ _ (chart_range p k n X Y f hp V) h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.IncomingRestriction

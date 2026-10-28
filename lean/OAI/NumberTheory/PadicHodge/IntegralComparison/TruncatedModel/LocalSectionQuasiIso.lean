import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedTruncated.FrameProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechLocalAcyclic
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechLocal
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SubchartResolution
import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ToInjectiveQuasiIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.QuasiIsoFunctorIso
import OAI.NumberTheory.PadicHodge.GeometricComparison.QuasiIsoRight

/-! # Local Section Quasi Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.LocalSectionQuasiIso.Cech

noncomputable section

/-! The actual global native comparison is a quasi-isomorphism on
sections over every affine intersection in the integral coordinate cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
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
local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.GeometricSliceDiagram.diagram p k n X Y f hp I

local instance localSeparated : IsSeparated wI := BoundedTruncated.FrameProduct.structureMap_separated p k C
local instance globalSeparated : IsSeparated w := by dsimp only [Witt.Crystalline.wittStructureMap]; infer_instance
local instance chartOpen : IsOpenImmersion g := Truncated.AffineModelFrame.chart_open p k n X Y f hp I.val I.property

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechGeometricTotal.restriction p k n X Y f hp I

variable (J : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
  (J := Ideal.span {(p : WittVector p k)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
  (Witt.Crystalline.wittStructureMap p k Y) n))

local notation "CoeffR" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)
abbrev extSections := CechLocalAcyclic.Comparison.extSections p k n X Y f I
local notation "E" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.LocalSectionQuasiIso.Cech.extSections p k n X Y f I
local notation "FI" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.AffineModelFrame.localFrame p k n X Y f hp I.val I.property

variable (i : AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.Index (Truncated.Witt.Ring p k n) X)
  (hi : I.val ≤ (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.opens (Truncated.Witt.Ring p k n) X i).val)

include hi in
theorem chartMap_ext_quasiIso : QuasiIso (((E).mapHomologicalComplex (.up ℕ)).map
    (CechChartMap.map p k n X Y f hp I)) :=
  CechChartMap.sections_quasiIso.{1, 2}
    p k n X Y f hp I CoeffR E i hi

include hi in
theorem globalMap_ext_quasiIso : QuasiIso (((E).mapHomologicalComplex (.up ℕ)).map
    (CechLocal.Comparison.globalMap p k n X Y f hp I J)) := by
  exact GeometricComparison.QuasiIsoRight.QuasiIsoFunctorComposition.right ((E).mapHomologicalComplex (.up ℕ))
    (CechChartMap.map p k n X Y f hp I) (CechLocal.Comparison.globalMap p k n X Y f hp I J)
    (chartMap_ext_quasiIso p k n X Y f hp I i hi)
    (CechLocalAcyclic.Comparison.localMap_quasiIso p k n X Y f hp I J i hi)

include hi in
theorem globalMap_sections_quasiIso : QuasiIso
    (((Sheaf.PresheafSectionComplex.sectionFunctor.{1, 0, 1, 2} CoeffR (BoundedCrystalline.Site.topology wI n)).mapHomologicalComplex (.up ℕ)).map
      (CechLocal.Comparison.globalMap p k n X Y f hp I J)) := by
  let := globalMap_ext_quasiIso p k n X Y f hp I J i hi
  exact QuasiIsoFunctorIso.transport _ _ (NatIso.mapHomologicalComplex
    (Ext.ZeroPresheafSections.iso.{1, 0, 1, 2} CoeffR (BoundedCrystalline.Site.topology wI n)) (.up ℕ))
    (CechLocal.Comparison.globalMap p k n X Y f hp I J)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.LocalSectionQuasiIso.Cech

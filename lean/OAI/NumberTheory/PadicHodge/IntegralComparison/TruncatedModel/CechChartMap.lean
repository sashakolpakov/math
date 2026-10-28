import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedTruncated.FrameProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechGeometricTotal
import OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.ChartTotalCoefficient

/-! # Cech Chart Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechChartMap

noncomputable section

/-! The actual local frame resolution maps canonically into the
restricted global native Cech total; additive section functors preserve
this map as a quasi-isomorphism on every covered affine subchart. -/

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

local notation "L" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechGeometricTotal.localSheafification p k n X Y f I
local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.GeometricSliceDiagram.meet_isIso p k n X Y f hp I

def map := (CechGeometricTotal.localFrameIso p k n X Y f hp I).inv ≫
  ((L).mapHomologicalComplex (.up ℕ)).map
    (GeometricComparison.Semilattice.ChartTotal.SemilatticeChartTotal.map X.left.affineOpens U I P H) ≫
  (CechGeometricTotal.iso p k n X Y f hp I).inv

universe r s
variable (R : Type r) [CommRing R]
  (F : BoundedCrystalline.Site.ModuleSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k (Truncated.AffineModelFrame.targetRing p k n X Y f I.val))) n
      ⥤ ModuleCat.{max r s} R) [F.Additive]
  (i : AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.Index (Truncated.Witt.Ring p k n) X)
  (hi : I ≤ CechSliceResolution.opens p k n X i)

include hi in
theorem sections_quasiIso : QuasiIso ((F.mapHomologicalComplex (.up ℕ)).map (CechChartMap.map p k n X Y f hp I)) := by
  have hmiddle : QuasiIso ((F.mapHomologicalComplex (.up ℕ)).map
      (((L).mapHomologicalComplex (.up ℕ)).map (GeometricComparison.Semilattice.ChartTotal.SemilatticeChartTotal.map X.left.affineOpens U I P H))) :=
    GeometricComparison.Semilattice.ChartTotalCoefficient.SemilatticeChartTotalCoefficient.quasiIso X.left.affineOpens I R (L ⋙ F) P H U i hi
  let er := (F.mapHomologicalComplex (.up ℕ)).mapIso (CechGeometricTotal.iso p k n X Y f hp I)
  have hr : QuasiIso er.inv := inferInstance
  rw [CechChartMap.map, CategoryTheory.Functor.map_comp]
  erw [CategoryTheory.Functor.map_comp]
  apply (quasiIso_iff_comp_left _ _).mpr
  apply (quasiIso_iff_comp_right _ er.inv (hφ' := hr)).mpr
  exact hmiddle

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechChartMap

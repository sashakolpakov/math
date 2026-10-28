import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechTotal
import OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.ChartTotalCoefficient

/-! # Cech Chart Map -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechChartMap.IntrinsicPadicCechChartMap

noncomputable section

/-! The actual local frame resolution maps canonically into the
restricted global native Cech total; additive section functors preserve
this map as a quasi-isomorphism on every covered affine subchart. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
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
local notation "P" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SliceDiagram.IntrinsicPadicGeometricSliceDiagram.diagram p X Y f hp n I

local instance localSeparated : IsSeparated wI := IntegralComparison.BoundedSmooth.WittFrameProduct.structureMap_separated p (ZMod p) C
local instance globalSeparated : IsSeparated w := by dsimp only [IntegralComparison.Witt.Crystalline.wittStructureMap]; infer_instance
local instance chartOpen : IsOpenImmersion g := ChartImage.IntrinsicPadicOpenFrame.chart_open p X Y f hp I.val I.property

local notation "L" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechTotal.IntrinsicPadicCechGeometricTotal.localSheafification p X Y f n I
local notation "H" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SliceDiagram.IntrinsicPadicGeometricSliceDiagram.meet_isIso p X Y f hp n I

def map := (CechTotal.IntrinsicPadicCechGeometricTotal.localFrameIso p X Y f hp n I).inv ≫
  ((L).mapHomologicalComplex (.up ℕ)).map
    (Semilattice.ChartTotal.SemilatticeChartTotal.map X.left.affineOpens U I P H) ≫
  (CechTotal.IntrinsicPadicCechGeometricTotal.iso p X Y f hp n I).inv

universe r s
variable (R : Type r) [CommRing R]
  (F : IntegralComparison.BoundedCrystalline.Site.ModuleSheaf (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p)
      (IntegralComparison.Crystalline.Presentation.affineScheme (ZMod p) (AffineFrame.IntrinsicPadicAffineFrame.targetRing p X Y f I.val))) n
      ⥤ ModuleCat.{max r s} R) [F.Additive]
  (i : Integral.EtaleAffineCover.IntegralEtaleAffineCover.Index ℤ_[p] X)
  (hi : I ≤ CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X i)

include hi in
theorem sections_quasiIso : QuasiIso ((F.mapHomologicalComplex (.up ℕ)).map (IntrinsicPadicCechChartMap.map p X Y f hp n I)) := by
  have hmiddle : QuasiIso ((F.mapHomologicalComplex (.up ℕ)).map
      (((L).mapHomologicalComplex (.up ℕ)).map (Semilattice.ChartTotal.SemilatticeChartTotal.map X.left.affineOpens U I P H))) :=
    Semilattice.ChartTotalCoefficient.SemilatticeChartTotalCoefficient.quasiIso X.left.affineOpens I R (L ⋙ F) P H U i hi
  let er := (F.mapHomologicalComplex (.up ℕ)).mapIso (CechTotal.IntrinsicPadicCechGeometricTotal.iso p X Y f hp n I)
  have hr : QuasiIso er.inv := inferInstance
  rw [IntrinsicPadicCechChartMap.map, CategoryTheory.Functor.map_comp]
  erw [CategoryTheory.Functor.map_comp]
  apply (quasiIso_iff_comp_left _ _).mpr
  apply (quasiIso_iff_comp_right _ er.inv (hφ' := hr)).mpr
  exact hmiddle

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechChartMap.IntrinsicPadicCechChartMap

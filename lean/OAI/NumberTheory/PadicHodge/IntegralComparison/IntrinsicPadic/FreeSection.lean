import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechLocal
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SubchartResolution
import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ToInjectiveQuasiIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.QuasiIsoFunctorIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.SubchartFreeAcyclicity
import OAI.NumberTheory.PadicHodge.GeometricComparison.QuasiIsoRight

/-! # Free Section -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.FreeSection.IntrinsicComparison

noncomputable section

/-! The actual global native comparison is a quasi-isomorphism on
sections over every affine intersection in the integral coordinate cover. -/

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

local instance localSeparated : IsSeparated wI := BoundedSmooth.WittFrameProduct.structureMap_separated p (ZMod p) C
local instance globalSeparated : IsSeparated w := by dsimp only [Witt.Crystalline.wittStructureMap]; infer_instance
local instance chartOpen : IsOpenImmersion g := GeometricComparison.IntrinsicPadic.ChartImage.IntrinsicPadicOpenFrame.chart_open p X Y f hp I.val I.property

local notation "R" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechTotal.IntrinsicPadicCechGeometricTotal.restriction p X Y f hp n I

variable (J : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
  (J := Ideal.span {(p : WittVector p (ZMod p))})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
  (Witt.Crystalline.wittStructureMap p (ZMod p) Y) n))

local notation "B" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
variable (V : BoundedCrystalline.Site.Objects (p := p)
  (J := Ideal.span {(p : WittVector p (ZMod p))})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
  (Witt.Crystalline.wittStructureMap p (ZMod p)
    (Crystalline.Presentation.affineScheme (ZMod p)
      (GeometricComparison.IntrinsicPadic.AffineFrame.IntrinsicPadicAffineFrame.targetRing p X Y f I.val))) n)

abbrev extSections := Ext.ModuleFunctor.functor.{2,1,2,1} B
  (Bounded.FreeYonedaAcyclicity.source p (ZMod p)
    (J := Ideal.span {(p : W)}) (δ := γ) wI n V) 0
local notation "E" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.FreeSection.IntrinsicComparison.extSections p X Y f n I V
local notation "FI" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.AffineFrame.IntrinsicPadicAffineFrame.frame p X Y f hp I.val I.property n

variable (i : GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCover.Index ℤ_[p] X)
  (hi : I.val ≤ GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens ℤ_[p] X i)

include hi in
theorem localMap_quasiIso : QuasiIso (((E).mapHomologicalComplex (.up ℕ)).map
    (GeometricComparison.IntrinsicPadic.CechLocal.IntrinsicPadicCechLocalComparison.map p X Y f hp n I J)) := by
  let : QuasiIso (Bounded.RelativeSheafComplex.augmentation wI n FI) :=
    GeometricComparison.IntrinsicPadic.SubchartResolution.IntrinsicPadicSubchartResolution.augmentation_quasiIso p X Y f hp n I i hi
  exact Acyclic.ToInjectiveQuasiIso.quasiIso B (Bounded.FreeYonedaAcyclicity.source p (ZMod p) wI n V)
    (Bounded.RelativeSheafComplex.complex wI n FI) (Bounded.RelativeSheafComplex.augmentation wI n FI)
    (fun a q => SubchartFreeAcyclicity.Intrinsic.acyclic p X Y f hp n I i hi V a q)
    (GeometricComparison.IntrinsicPadic.CechLocal.IntrinsicPadicCechLocalComparison.resolution p X Y f hp n I J)
    (GeometricComparison.IntrinsicPadic.CechLocal.IntrinsicPadicCechLocalComparison.map p X Y f hp n I J)
    (GeometricComparison.IntrinsicPadic.CechLocal.IntrinsicPadicCechLocalComparison.augmentation p X Y f hp n I J)

include hi in
theorem chartMap_quasiIso : QuasiIso (((E).mapHomologicalComplex (.up ℕ)).map
    (GeometricComparison.IntrinsicPadic.CechChartMap.IntrinsicPadicCechChartMap.map p X Y f hp n I)) :=
  GeometricComparison.IntrinsicPadic.CechChartMap.IntrinsicPadicCechChartMap.sections_quasiIso.{1,2} p X Y f hp n I B E i hi

include hi in
theorem globalMap_quasiIso : QuasiIso (((E).mapHomologicalComplex (.up ℕ)).map
    (GeometricComparison.IntrinsicPadic.CechLocal.IntrinsicPadicCechLocalComparison.globalMap p X Y f hp n I J)) :=
  GeometricComparison.QuasiIsoRight.QuasiIsoFunctorComposition.right ((E).mapHomologicalComplex (.up ℕ))
    (GeometricComparison.IntrinsicPadic.CechChartMap.IntrinsicPadicCechChartMap.map p X Y f hp n I)
    (GeometricComparison.IntrinsicPadic.CechLocal.IntrinsicPadicCechLocalComparison.globalMap p X Y f hp n I J)
    (chartMap_quasiIso p X Y f hp n I V i hi)
    (localMap_quasiIso p X Y f hp n I J V i hi)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.FreeSection.IntrinsicComparison

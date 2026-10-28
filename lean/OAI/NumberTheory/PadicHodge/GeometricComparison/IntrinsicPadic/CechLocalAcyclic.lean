import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechLocal
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SubchartResolution
import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ToInjectiveQuasiIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.QuasiIsoFunctorIso

/-! # Cech Local Acyclic -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechLocalAcyclic.IntrinsicPadicCechLocalAcyclicComparison

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

local instance localSeparated : IsSeparated wI := IntegralComparison.BoundedSmooth.WittFrameProduct.structureMap_separated p (ZMod p) C
local instance globalSeparated : IsSeparated w := by dsimp only [IntegralComparison.Witt.Crystalline.wittStructureMap]; infer_instance
local instance chartOpen : IsOpenImmersion g := ChartImage.IntrinsicPadicOpenFrame.chart_open p X Y f hp I.val I.property

local notation "R" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechTotal.IntrinsicPadicCechGeometricTotal.restriction p X Y f hp n I

variable (J : InjectiveResolution (IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
  (J := Ideal.span {(p : WittVector p (ZMod p))})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
  (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y) n))

local notation "B" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
abbrev extSections := IntegralComparison.Ext.ModuleFunctor.functor.{2, 1, 2, 1} B
  (IntegralComparison.BoundedCrystalline.CrystallineCohomology.constantUnit (p := p) (J := Ideal.span {(p : W)}) (δ := γ) wI n) 0
local notation "E" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechLocalAcyclic.IntrinsicPadicCechLocalAcyclicComparison.extSections p X Y f n I
local notation "FI" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.AffineFrame.IntrinsicPadicAffineFrame.frame p X Y f hp I.val I.property n

variable (i : Integral.EtaleAffineCover.IntegralEtaleAffineCover.Index ℤ_[p] X)
  (hi : I.val ≤ Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens ℤ_[p] X i)

include hi in
theorem localMap_quasiIso : QuasiIso (((E).mapHomologicalComplex (.up ℕ)).map
    (CechLocal.IntrinsicPadicCechLocalComparison.map p X Y f hp n I J)) := by
  let : QuasiIso (IntegralComparison.Bounded.RelativeSheafComplex.augmentation wI n FI) :=
    SubchartResolution.IntrinsicPadicSubchartResolution.augmentation_quasiIso p X Y f hp n I i hi
  exact IntegralComparison.Acyclic.ToInjectiveQuasiIso.quasiIso B (IntegralComparison.BoundedCrystalline.CrystallineCohomology.constantUnit wI n)
    (IntegralComparison.Bounded.RelativeSheafComplex.complex wI n FI) (IntegralComparison.Bounded.RelativeSheafComplex.augmentation wI n FI)
    (fun a q => SubchartResolution.IntrinsicPadicSubchartResolution.acyclic p X Y f hp n I i hi a q)
    (CechLocal.IntrinsicPadicCechLocalComparison.resolution p X Y f hp n I J)
    (CechLocal.IntrinsicPadicCechLocalComparison.map p X Y f hp n I J)
    (CechLocal.IntrinsicPadicCechLocalComparison.augmentation p X Y f hp n I J)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechLocalAcyclic.IntrinsicPadicCechLocalAcyclicComparison

import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.LocalSectionQuasiIso
import OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.ChartSectionFunctorIso
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ChartImage

/-! # Zariski Section Quasi Iso -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ZariskiSectionQuasiIso.IntrinsicPadicCechZariskiSectionQuasiIso

noncomputable section

/-! The original global native comparison is a quasi-isomorphism on
Zariski sections of each affine subchart in the integral coordinate cover. -/

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

def map := ((IntegralComparison.BoundedOpen.SectionComplex.functor (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n).mapHomologicalComplex (.up ℕ)).map
  (CechInjective.IntrinsicPadicCechInjectiveComparison.map p X Y f hp n J)

variable (i : Integral.EtaleAffineCover.IntegralEtaleAffineCover.Index ℤ_[p] X)
  (hi : I.val ≤ Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens ℤ_[p] X i)

include hi in
theorem evaluation_quasiIso : QuasiIso
    (((IntegralComparison.BoundedOpen.SectionComplex.evaluation (B := W) (f ⁻¹ᵁ I.val)).mapHomologicalComplex (.up ℕ)).map
      (IntrinsicPadicCechZariskiSectionQuasiIso.map p X Y f hp n J)) := by
  let : QuasiIso (((IntegralComparison.Bounded.PostcomposeTopology.restriction g hg n ⋙
      IntegralComparison.Sheaf.PresheafSectionComplex.sectionFunctor.{1, 0, 1, 2}
        (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := W))
        (IntegralComparison.BoundedCrystalline.Site.topology wI n)).mapHomologicalComplex (.up ℕ)).map
      (CechInjective.IntrinsicPadicCechInjectiveComparison.map p X Y f hp n J)) :=
    LocalSectionQuasiIso.IntrinsicPadicCechLocalSectionQuasiIso.globalMap_sections_quasiIso p X Y f hp n I J i hi
  have h := IntegralComparison.QuasiIsoFunctorIso.transport _ _
    (NatIso.mapHomologicalComplex (Bounded.ChartSectionFunctorIso.BoundedChartSectionFunctorIso.iso g hg n) (.up ℕ))
    (CechInjective.IntrinsicPadicCechInjectiveComparison.map p X Y f hp n J)
  erw [ChartImage.IntrinsicPadicChartImage.opensRange] at h
  exact h

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ZariskiSectionQuasiIso.IntrinsicPadicCechZariskiSectionQuasiIso

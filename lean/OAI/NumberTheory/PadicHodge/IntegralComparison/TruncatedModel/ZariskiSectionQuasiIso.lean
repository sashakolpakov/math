import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedTruncated.FrameProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.LocalSectionQuasiIso
import OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.ChartSectionFunctorIso

/-! # Zariski Section Quasi Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ZariskiSectionQuasiIso.Cech

noncomputable section

/-! The original global native comparison is a quasi-isomorphism on
Zariski sections of each affine subchart in the integral coordinate cover. -/

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

def map := ((BoundedOpen.SectionComplex.functor (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n).mapHomologicalComplex (.up ℕ)).map
  (CechInjective.Comparison.map p k n X Y f hp J)

variable (i : AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.Index (Truncated.Witt.Ring p k n) X)
  (hi : I.val ≤ (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.opens (Truncated.Witt.Ring p k n) X i).val)

include hi in
theorem evaluation_quasiIso : QuasiIso
    (((BoundedOpen.SectionComplex.evaluation (B := W) (f ⁻¹ᵁ I.val)).mapHomologicalComplex (.up ℕ)).map
      (Cech.map p k n X Y f hp J)) := by
  let : QuasiIso (((Bounded.PostcomposeTopology.restriction g hg n ⋙
      Sheaf.PresheafSectionComplex.sectionFunctor.{1, 0, 1, 2}
        (Crystalline.ExactRestriction.Coeff (B := W))
        (BoundedCrystalline.Site.topology wI n)).mapHomologicalComplex (.up ℕ)).map
      (CechInjective.Comparison.map p k n X Y f hp J)) :=
    LocalSectionQuasiIso.Cech.globalMap_sections_quasiIso p k n X Y f hp I J i hi
  have h := QuasiIsoFunctorIso.transport _ _
    (NatIso.mapHomologicalComplex (GeometricComparison.Bounded.ChartSectionFunctorIso.BoundedChartSectionFunctorIso.iso g hg n) (.up ℕ))
    (CechInjective.Comparison.map p k n X Y f hp J)
  have hj : (g).opensRange = f ⁻¹ᵁ I.val :=
    IsAffineOpen.opensRange_fromSpec (Truncated.AffineModelFrame.residue_affine p k n X Y f hp I.val I.property)
  erw [hj] at h
  exact h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ZariskiSectionQuasiIso.Cech

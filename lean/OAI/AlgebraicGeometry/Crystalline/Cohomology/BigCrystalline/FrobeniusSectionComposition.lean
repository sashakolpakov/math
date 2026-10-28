import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.AffineFrobeniusSectionCoordinates
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.TwistSectionCoordinates

/-! # Frobenius Section Composition -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrobeniusSectionComposition.BigCrystallineFrobeniusSectionComposition

noncomputable section

/-! # Composing the actual geometric and coefficient-twist section formulas -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) (hp : p.Prime) (W A σ : Type u) [CommRing W] [CommRing A]
  (hA : (p : A) = 0) (J : Ideal W) (δ : DividedPowers J)
  (base : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of W))
  (e : W ≃+* W) (he : DividedPowers.IsDPMorphism δ δ e.toRingHom)
  (he' : DividedPowers.IsDPMorphism δ δ e.symm.toRingHom)
  (h : Spec.map (CommRingCat.ofHom (Picard.Homomorphisms.Frobenius.Construction.powerRingHom p hp A hA)) ≫ base =
    base ≫ Spec.map (CommRingCat.ofHom e.toRingHom))
  (a : σ → A) [Fintype σ] [LinearOrder σ]

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := W)
local notation "φ" => OAI.AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.powerRingHom p hp A hA
local notation "bF" => Spec.map (CommRingCat.ofHom φ) ≫ base
local notation "tw" => OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineBaseTwist.twist (p := p) e he h
local notation "geo" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.PullbackLifts.BigCrystallinePullbackLifts.postcompose p W A A J δ base φ
local notation "U" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite.Object.topology (p := p) (J := J) (δ := δ) (f := base)
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite.Object.topology (p := p) (J := J) (δ := δ) (f := bF)
local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameSheafResolution.BigCrystallineFrameSheafResolution.complex p W A J δ base a
local notation "L" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameSheafResolution.BigCrystallineFrameSheafResolution.complex p W A J δ bF a
local notation "A₀" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.constantUnit (p := p) (J := J) (δ := δ) base
local notation "c" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.AffineFrobeniusSheaves.BigCrystallineAffineFrobeniusSheaves.complexMap p hp W A σ hA J δ base a
local notation "t" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.TwistSheafTransport.BigCrystallineTwistSheafTransport.complexIso p W A J δ base bF e he he' h a

def transport (j : ℕ) (x : A₀ ⟶ (K).X j) : A₀ ⟶ (K).X j :=
  TwistSectionCoordinates.BigCrystallineTwistSectionCoordinates.transport p W A J δ base bF e he he' h a j
    (AffineFrobeniusSectionCoordinates.BigCrystallineAffineFrobeniusSectionCoordinates.transport p hp W A σ hA J δ base a j x)

theorem sections_apply (j : ℕ) (x : A₀ ⟶ (K).X j)
    (V : (FrameLifts.BigCrystallineFrameLifts.Site p W A J δ base)ᵒᵖ) :
    (NumberTheory.PadicHodge.IntegralComparison.Ext.ZeroPresheafSections.homLinearEquiv R U ((K).X j)
      (transport p hp W A σ hA J δ base e he he' h a j x)).app V (1 : R) =
    ((t).hom.f j).hom.app V
      (((c).f j).hom.app ((tw).op.obj V)
        ((NumberTheory.PadicHodge.IntegralComparison.Ext.ZeroPresheafSections.homLinearEquiv R U ((K).X j) x).app
          ((geo).op.obj ((tw).op.obj V)) (1 : R))) := by
  let y := AffineFrobeniusSectionCoordinates.BigCrystallineAffineFrobeniusSectionCoordinates.transport p hp W A σ hA J δ base a j x
  let f : ((L).X j).obj.obj ((tw).op.obj V) → ((K).X j).obj.obj V :=
    fun z => ((t).hom.f j).hom.app V z
  have ht := TwistSectionCoordinates.BigCrystallineTwistSectionCoordinates.sections_apply p W A J δ base bF e he he' h a j y V
  dsimp only [TwistSectionCoordinates.BigCrystallineTwistSectionCoordinates.targetSections,
    TwistSectionCoordinates.BigCrystallineTwistSectionCoordinates.sourceSections, y] at ht
  have hg := AffineFrobeniusSectionCoordinates.BigCrystallineAffineFrobeniusSectionCoordinates.sections_apply p hp W A σ hA J δ base a j x
    ((tw).op.obj V)
  let v₁ : ((L).X j).obj.obj ((tw).op.obj V) :=
    (NumberTheory.PadicHodge.IntegralComparison.Ext.ZeroPresheafSections.homLinearEquiv R T ((L).X j) y).app ((tw).op.obj V) (1 : R)
  let v₂ : ((L).X j).obj.obj ((tw).op.obj V) :=
    ((c).f j).hom.app ((tw).op.obj V)
      ((NumberTheory.PadicHodge.IntegralComparison.Ext.ZeroPresheafSections.homLinearEquiv R U ((K).X j) x).app
        ((geo).op.obj ((tw).op.obj V)) (1 : R))
  have hgeo : v₁ = v₂ := hg
  have htw :
      (NumberTheory.PadicHodge.IntegralComparison.Ext.ZeroPresheafSections.homLinearEquiv R U ((K).X j)
        (transport p hp W A σ hA J δ base e he he' h a j x)).app V (1 : R) = f v₁ := by
    dsimp only [transport, f, v₁, y]
    convert ht using 1
  exact htw.trans (congrArg f hgeo)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrobeniusSectionComposition.BigCrystallineFrobeniusSectionComposition

import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrobeniusSectionComposition
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrobeniusTransport
import OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafificationRestriction

/-! # Frobenius Section Generators -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrobeniusSectionGenerators.BigCrystallineFrobeniusSectionGenerators

noncomputable section

/-! # Original Frobenius transports a represented frame section through the actual raw maps -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

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
local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameLifts.BigCrystallineFrameLifts.Site p W A J δ base
local notation "tw" => OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineBaseTwist.twist (p := p) e he h
local notation "U" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite.Object.topology (p := p) (J := J) (δ := δ) (f := base)
local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameSheafResolution.BigCrystallineFrameSheafResolution.complex p W A J δ base a
local notation "L" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameSheafResolution.BigCrystallineFrameSheafResolution.complex p W A J δ bF a
local notation "A₀" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.constantUnit (p := p) (J := J) (δ := δ) base
local notation "c" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.AffineFrobeniusSheaves.BigCrystallineAffineFrobeniusSheaves.complexMap p hp W A σ hA J δ base a
local notation "t" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.TwistSheafTransport.BigCrystallineTwistSheafTransport.complexIso p W A J δ base bF e he he' h a

def sections (j : ℕ) (x : A₀ ⟶ (K).X j) :=
  NumberTheory.PadicHodge.IntegralComparison.Ext.ZeroPresheafSections.homLinearEquiv R U ((K).X j) x

def generator (j : ℕ) : FrobeniusTransport.BigCrystallineFrobeniusRawTransport.presheaf p W A σ J δ base a j ⟶
    ((K).X j).obj :=
  toSheafify U (FrobeniusTransport.BigCrystallineFrobeniusRawTransport.presheaf p W A σ J δ base a j)

theorem section_generator (j : ℕ) (x : A₀ ⟶ (K).X j) (Q : C)
    (f : (FrobeniusTransport.BigCrystallineFrobeniusRawTransport.transformed p hp W A hA J δ base e he h).obj Q ⟶ Q)
    (z : (FrobeniusTransport.BigCrystallineFrobeniusRawTransport.presheaf p W A σ J δ base a j).obj (op Q))
    (hz : (generator p W A σ J δ base a j).app (op Q) z =
      (sections p W A σ J δ base a j x).app (op Q) (1 : R)) :
    (sections p W A σ J δ base a j
      (FrobeniusSectionComposition.BigCrystallineFrobeniusSectionComposition.transport p hp W A σ hA J δ base e he he' h a j x)).app
        (op Q) (1 : R) =
      (generator p W A σ J δ base a j).app (op Q)
        (FrobeniusTransport.BigCrystallineFrobeniusRawTransport.map p hp W A σ hA J δ base e he h a j Q f z) := by
  let y := (FrobeniusTransport.BigCrystallineFrobeniusRawTransport.presheaf p W A σ J δ base a j).map f.op z
  let y' := (AffineFrobeniusSectionCoordinates.BigCrystallineAffineFrobeniusSectionCoordinates.rawMap p hp W A σ hA J δ base a j).app
    (op ((tw).obj Q)) y
  have hs := FrobeniusSectionComposition.BigCrystallineFrobeniusSectionComposition.sections_apply p hp W A σ hA J δ base e he he' h a j x (op Q)
  have hm := SheafificationRestriction.SheafificationRestrictionGenerators.section_generator
    (generator p W A σ J δ base a j) (ModuleCat.of R R)
    (sections p W A σ J δ base a j x) f.op (1 : R) z hz.symm
  have hg := congrArg (fun m => m.app (op ((tw).obj Q)) y)
    (AffineFrobeniusSectionCoordinates.BigCrystallineAffineFrobeniusSectionCoordinates.generator p hp W A σ hA J δ base a j)
  dsimp only [NatTrans.comp_app, ModuleCat.comp_apply, Functor.whiskerLeft_app] at hg
  have ht := TwistGeneratorCoordinates.BigCrystallineTwistGeneratorCoordinates.generator_apply p W A J δ base bF e he he' h a j (op Q) y'
  let applyTwist : ((L).X j).obj.obj (op ((tw).obj Q)) → ((K).X j).obj.obj (op Q) :=
    ScalarRestricted.ScalarRestrictedAdditiveMap.map (NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistCohomology.coefficientEquiv e).symm.toRingHom
      (((t).hom.f j).hom.app (op Q))
  have hgt := congrArg applyTwist hg
  dsimp only [AffineFrobeniusSectionCoordinates.BigCrystallineAffineFrobeniusSectionCoordinates.targetPresheaf,
    TwistGeneratorCoordinates.BigCrystallineTwistGeneratorCoordinates.sourcePresheaf] at hgt ht
  have hraw := FrobeniusTransport.BigCrystallineFrobeniusRawTransport.map_apply p hp W A σ hA J δ base e he h a j Q f z
  have hlast := congrArg (fun z => (generator p W A σ J δ base a j).app (op Q) z) hraw
  have hchain := hs.trans
    ((congrArg (fun v => applyTwist (((c).f j).hom.app (op ((tw).obj Q)) v)) hm).trans
      (hgt.trans ht))
  dsimp only [sections]
  convert hchain.trans hlast.symm using 1

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrobeniusSectionGenerators.BigCrystallineFrobeniusSectionGenerators

import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.AffineFrobeniusSectionCoordinates
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.TwistGeneratorCoordinates
import OAI.AlgebraicGeometry.Crystalline.Cohomology.ScalarRestricted

/-! # Frobenius Transport -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrobeniusTransport.BigCrystallineFrobeniusRawTransport

noncomputable section

/-! # Compose the original raw frame transports at an arbitrary Frobenius frame morphism -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable (p : ℕ) (hp : p.Prime) (W A σ : Type u) [CommRing W] [CommRing A]
  (hA : (p : A) = 0) (J : Ideal W) (δ : DividedPowers J)
  (base : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of W))
  (e : W ≃+* W) (he : DividedPowers.IsDPMorphism δ δ e.toRingHom)
  (h : Spec.map (CommRingCat.ofHom (Picard.Homomorphisms.Frobenius.Construction.powerRingHom p hp A hA)) ≫ base =
    base ≫ Spec.map (CommRingCat.ofHom e.toRingHom))
  (a : σ → A) [Fintype σ] [LinearOrder σ]

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := W)
local notation "φ" => OAI.AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.powerRingHom p hp A hA
local notation "bF" => Spec.map (CommRingCat.ofHom φ) ≫ base
local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameLifts.BigCrystallineFrameLifts.Site p W A J δ base
local notation "tw" => OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineBaseTwist.twist (p := p) e he h
local notation "geo" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.PullbackLifts.BigCrystallinePullbackLifts.postcompose p W A A J δ base φ
local notation "T" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.TwistSheafTransport.BigCrystallineTwistSheafTransport.largeRestriction W e

def presheaf (j : ℕ) : Cᵒᵖ ⥤ ModuleCat.{u + 1} R :=
  AffineFrobeniusSectionCoordinates.BigCrystallineAffineFrobeniusSectionCoordinates.sourcePresheaf p W A σ J δ base a j

def transformed : C ⥤ C := tw ⋙ geo

def restrictionHom (j : ℕ) (Q : C)
    (f : (transformed p hp W A hA J δ base e he h).obj Q ⟶ Q) :
    (presheaf p W A σ J δ base a j).obj (op Q) ⟶
      (presheaf p W A σ J δ base a j).obj
        (op ((transformed p hp W A hA J δ base e he h).obj Q)) :=
  (presheaf p W A σ J δ base a j).map f.op

def geometricHom (j : ℕ) (Q : C) :
    (presheaf p W A σ J δ base a j).obj
      (op ((transformed p hp W A hA J δ base e he h).obj Q)) ⟶
    (AffineFrobeniusSectionCoordinates.BigCrystallineAffineFrobeniusSectionCoordinates.targetPresheaf p hp W A σ hA J δ base a j).obj
      (op ((tw).obj Q)) :=
  (AffineFrobeniusSectionCoordinates.BigCrystallineAffineFrobeniusSectionCoordinates.rawMap p hp W A σ hA J δ base a j).app (op ((tw).obj Q))

def twistHom (j : ℕ) (Q : C) :
    (T).obj
      ((AffineFrobeniusSectionCoordinates.BigCrystallineAffineFrobeniusSectionCoordinates.targetPresheaf p hp W A σ hA J δ base a j).obj
        (op ((tw).obj Q))) ⟶ (presheaf p W A σ J δ base a j).obj (op Q) :=
  (TwistGeneratorCoordinates.BigCrystallineTwistGeneratorCoordinates.rawMap p W A J δ base bF e he h a j).app (op Q)

def mapHom (j : ℕ) (Q : C)
    (f : (transformed p hp W A hA J δ base e he h).obj Q ⟶ Q) :
    (T).obj ((presheaf p W A σ J δ base a j).obj (op Q)) ⟶
      (presheaf p W A σ J δ base a j).obj (op Q) :=
  (T).map (restrictionHom p hp W A σ hA J δ base e he h a j Q f ≫
    geometricHom p hp W A σ hA J δ base e he h a j Q) ≫
      twistHom p hp W A σ hA J δ base e he h a j Q

def map (j : ℕ) (Q : C)
    (f : (transformed p hp W A hA J δ base e he h).obj Q ⟶ Q)
    (z : (presheaf p W A σ J δ base a j).obj (op Q)) :
    (presheaf p W A σ J δ base a j).obj (op Q) :=
  ScalarRestricted.ScalarRestrictedAdditiveMap.map (NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistCohomology.coefficientEquiv e).symm.toRingHom
    (mapHom p hp W A σ hA J δ base e he h a j Q f) z

theorem map_apply (j : ℕ) (Q : C)
    (f : (transformed p hp W A hA J δ base e he h).obj Q ⟶ Q)
    (z : (presheaf p W A σ J δ base a j).obj (op Q)) :
    BigCrystallineFrobeniusRawTransport.map p hp W A σ hA J δ base e he h a j Q f z =
      ScalarRestricted.ScalarRestrictedAdditiveMap.map (NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistCohomology.coefficientEquiv e).symm.toRingHom
        (twistHom p hp W A σ hA J δ base e he h a j Q)
        ((geometricHom p hp W A σ hA J δ base e he h a j Q).hom
          ((restrictionHom p hp W A σ hA J δ base e he h a j Q f).hom z)) :=
  ScalarRestricted.ScalarRestrictedAdditiveMap.triple_comp_additive_apply
    (NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistCohomology.coefficientEquiv e).symm.toRingHom
    (restrictionHom p hp W A σ hA J δ base e he h a j Q f)
    (geometricHom p hp W A σ hA J δ base e he h a j Q)
    (twistHom p hp W A σ hA J δ base e he h a j Q) z

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrobeniusTransport.BigCrystallineFrobeniusRawTransport

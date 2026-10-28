import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.AffineFrobeniusSheaves
import OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafSectionHomEquiv
import OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafificationMap
import OAI.AlgebraicGeometry.Crystalline.Cohomology.ExtZero
import OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ZeroPresheafSections

/-! # Affine Frobenius Section Coordinates -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.AffineFrobeniusSectionCoordinates.BigCrystallineAffineFrobeniusSectionCoordinates

noncomputable section

/-! # Original geometric Frobenius sections and their actual frame generators -/

open _root_.CategoryTheory _root_.CategoryTheory.Functor _root_.AlgebraicGeometry

open _root_.CategoryTheory.Abelian

universe u

variable (p : ℕ) (hp : p.Prime) (W A σ : Type u) [CommRing W] [CommRing A]
  (hA : (p : A) = 0) (J : Ideal W) (δ : DividedPowers J)
  (base : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of W))
  (a : σ → A) [Fintype σ] [LinearOrder σ]

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := W)
local notation "φ" => OAI.AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.powerRingHom p hp A hA
local notation "g" => Spec.map (CommRingCat.ofHom φ)
local notation "bF" => g ≫ base
local notation "ι" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.PullbackLifts.BigCrystallinePullbackLifts.postcompose p W A A J δ base φ
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite.Object.topology (p := p) (J := J) (δ := δ) (f := bF)
local notation "U" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite.Object.topology (p := p) (J := J) (δ := δ) (f := base)
local notation "F" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.PullbackSheafTransport.BigCrystallinePullbackSheafTransport.restriction p W A A J δ base φ
local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameSheafResolution.BigCrystallineFrameSheafResolution.complex p W A J δ base a
local notation "L" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameSheafResolution.BigCrystallineFrameSheafResolution.complex p W A J δ bF a
local notation "A₀" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.constantUnit (p := p) (J := J) (δ := δ) base
local notation "A₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.constantUnit (p := p) (J := J) (δ := δ) bF
local notation "c" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.AffineFrobeniusSheaves.BigCrystallineAffineFrobeniusSheaves.complexMap p hp W A σ hA J δ base a
local notation "E" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameSheafResolution.BigCrystallineFrameSheafResolution.coefficientLift W

def transport (n : ℕ) (x : A₀ ⟶ (K).X n) : A₁ ⟶ (L).X n :=
  (NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.constantTransport (p := p) (J := J) (δ := δ) (fY := base) g rfl).inv ≫
    (F).map x ≫ (c).f n

theorem sections (n : ℕ) (x : A₀ ⟶ (K).X n) :
    NumberTheory.PadicHodge.IntegralComparison.Ext.ZeroPresheafSections.homLinearEquiv R T ((L).X n)
      (transport p hp W A σ hA J δ base a n x) =
    whiskerLeft (ι).op (NumberTheory.PadicHodge.IntegralComparison.Ext.ZeroPresheafSections.homLinearEquiv R U ((K).X n) x) ≫ ((c).f n).hom :=
  SheafSectionHomEquiv.SheafSectionRestriction.homEquiv T U ι (ModuleCat.of R R) ((K).X n) ((L).X n) x ((c).f n)

theorem ext_map_mk (n : ℕ) (x : A₀ ⟶ (K).X n) :
    (Ext.mk₀ (NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.constantTransport
      (p := p) (J := J) (δ := δ) (fY := base) g rfl).inv).comp
      (((Ext.mk₀ x).mapExactFunctor F).comp (Ext.mk₀ ((c).f n)) (add_zero 0)) (zero_add 0) =
    Ext.mk₀ (transport p hp W A σ hA J δ base a n x) :=
  ExtZero.ExtZeroTransport.mk F
    (NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.constantTransport (p := p) (J := J) (δ := δ) (fY := base) g rfl).inv
    ((c).f n) x

theorem sections_apply (n : ℕ) (x : A₀ ⟶ (K).X n)
    (V : (FrameLifts.BigCrystallineFrameLifts.Site p W A J δ bF)ᵒᵖ) :
    (NumberTheory.PadicHodge.IntegralComparison.Ext.ZeroPresheafSections.homLinearEquiv R T ((L).X n)
      (transport p hp W A σ hA J δ base a n x)).app V (1 : R) =
      ((c).f n).hom.app V
        ((NumberTheory.PadicHodge.IntegralComparison.Ext.ZeroPresheafSections.homLinearEquiv R U ((K).X n) x).app ((ι).op.obj V) (1 : R)) :=
  congrArg (fun s => s.app V (1 : R)) (sections p hp W A σ hA J δ base a n x)

def sourcePresheaf (n : ℕ) :=
  (FrameResolution.BigCrystallineFrameResolution.complex (p := p) (J := J) (δ := δ) (base := base) a).X n ⋙ E

def targetPresheaf (n : ℕ) :=
  (FrameResolution.BigCrystallineFrameResolution.complex (p := p) (J := J) (δ := δ) (base := bF) a).X n ⋙ E

def rawMap (n : ℕ) : (ι).op ⋙ sourcePresheaf p W A σ J δ base a n ⟶
    targetPresheaf p hp W A σ hA J δ base a n :=
  whiskerRight ((AffineFrobeniusFrames.BigCrystallineAffineFrobeniusFrames.complexMap p hp W A σ hA J δ base a).f n) E

theorem generator (n : ℕ) :
    whiskerLeft (ι).op (toSheafify U (sourcePresheaf p W A σ J δ base a n)) ≫ ((c).f n).hom =
      rawMap p hp W A σ hA J δ base a n ≫
        toSheafify T (targetPresheaf p hp W A σ hA J δ base a n) :=
  SheafificationMap.SheafificationMapGenerators.generator T U ι (sourcePresheaf p W A σ J δ base a n)
    (targetPresheaf p hp W A σ hA J δ base a n) (rawMap p hp W A σ hA J δ base a n)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.AffineFrobeniusSectionCoordinates.BigCrystallineAffineFrobeniusSectionCoordinates

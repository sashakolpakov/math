import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.TwistSheafTransport
import OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafSectionConstant
import OAI.AlgebraicGeometry.Crystalline.Cohomology.ExtZero
import OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistGenerators
import OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ZeroPresheafSections

/-! # Twist Section Coordinates -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.TwistSectionCoordinates.BigCrystallineTwistSectionCoordinates

noncomputable section

/-! # Original crystalline base-twist sections in presheaf coordinates -/

open _root_.CategoryTheory _root_.CategoryTheory.Functor _root_.AlgebraicGeometry

open _root_.CategoryTheory.Abelian

universe u

variable (p : ℕ) (W A : Type u) [CommRing W] [CommRing A]
  (J : Ideal W) (δ : DividedPowers J)
  (base base' : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of W))
  (e : W ≃+* W) (he : DividedPowers.IsDPMorphism δ δ e.toRingHom)
  (he' : DividedPowers.IsDPMorphism δ δ e.symm.toRingHom)
  (h : base' = base ≫ Spec.map (CommRingCat.ofHom e.toRingHom))

local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameLifts.BigCrystallineFrameLifts.Site p W A J δ base
local notation "D" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameLifts.BigCrystallineFrameLifts.Site p W A J δ base'
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := W)
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite.Object.topology (p := p) (J := J) (δ := δ) (f := base)
local notation "U" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite.Object.topology (p := p) (J := J) (δ := δ) (f := base')
local notation "ι" => OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineBaseTwist.twist (p := p) e he h
local notation "Q" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.TwistSheafTransport.BigCrystallineTwistSheafTransport.largeRestriction W e
local notation "F" => OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistCohomology.twistedRestriction (p := p) e he he' h
local notation "A₀" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.constantUnit (p := p) (J := J) (δ := δ) base
local notation "A₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.constantUnit (p := p) (J := J) (δ := δ) base'

def modelConstantTransport : (F).obj A₁ ≅ A₀ := by
  let := NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistRestriction.twist_continuous (p := p) e he he' h
  let := NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistRestriction.twist_cocontinuous (p := p) e he he' h
  exact SheafSectionConstant.SheafSectionCoefficientRestriction.constantTransport T U ι Q
    (ModuleCat.of R R) (ModuleCat.of R R)
    (ModuleCat.restrictScalarsIsoOfEquiv (NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistCohomology.coefficientEquiv e).symm)

theorem constant_transport_eq :
    NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistCohomology.constantTransport (p := p) e he he' h =
      modelConstantTransport p W A J δ base base' e he he' h := by
  let := NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistRestriction.twist_continuous (p := p) e he he' h
  let := NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistRestriction.twist_cocontinuous (p := p) e he he' h
  exact NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistGenerators.constantTransport_eq e he he' h

variable {σ : Type u} (a : σ → A) [Fintype σ] [LinearOrder σ]

local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameSheafResolution.BigCrystallineFrameSheafResolution.complex p W A J δ base a
local notation "L" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameSheafResolution.BigCrystallineFrameSheafResolution.complex p W A J δ base' a
local notation "c" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.TwistSheafTransport.BigCrystallineTwistSheafTransport.complexIso p W A J δ base base' e he he' h a

def sourceSections (n : ℕ) (x : A₁ ⟶ (L).X n) :
    (Functor.const Dᵒᵖ).obj (ModuleCat.of R R) ⟶ ((L).X n).obj :=
  NumberTheory.PadicHodge.IntegralComparison.Ext.ZeroPresheafSections.homLinearEquiv R U ((L).X n) x

def targetSections (n : ℕ) (x : A₀ ⟶ (K).X n) :
    (Functor.const Cᵒᵖ).obj (ModuleCat.of R R) ⟶ ((K).X n).obj :=
  NumberTheory.PadicHodge.IntegralComparison.Ext.ZeroPresheafSections.homLinearEquiv R T ((K).X n) x

def transport (n : ℕ) (x : A₁ ⟶ (L).X n) : A₀ ⟶ (K).X n :=
  (NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistCohomology.constantTransport (p := p) e he he' h).inv ≫ (F).map x ≫ (c).hom.f n

theorem sections (n : ℕ) (x : A₁ ⟶ (L).X n) :
    targetSections p W A J δ base a n (transport p W A J δ base base' e he he' h a n x) =
      (NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistGenerators.constantPresheafTransport (p := p) e he h).inv ≫
        whiskerRight (whiskerLeft (ι).op (sourceSections p W A J δ base' a n x)) Q ≫
          ((c).hom.f n).hom := by
  let := NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistRestriction.twist_continuous (p := p) e he he' h
  let := NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistRestriction.twist_cocontinuous (p := p) e he he' h
  have hx : transport p W A J δ base base' e he he' h a n x =
      (modelConstantTransport p W A J δ base base' e he he' h).inv ≫ (F).map x ≫ (c).hom.f n :=
    congrArg (fun t : (F).obj A₁ ≅ A₀ => t.inv ≫ (F).map x ≫ (c).hom.f n)
      (constant_transport_eq p W A J δ base base' e he he' h)
  have hs := SheafSectionConstant.SheafSectionCoefficientRestriction.homEquiv T U ι Q
    (ModuleCat.of R R) (ModuleCat.of R R)
    (ModuleCat.restrictScalarsIsoOfEquiv (NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistCohomology.coefficientEquiv e).symm)
    ((L).X n) ((K).X n) x ((c).hom.f n)
  exact (congrArg (targetSections p W A J δ base a n) hx).trans hs

theorem ext_map_mk (n : ℕ) (x : A₁ ⟶ (L).X n) :
    (Ext.mk₀ (NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistCohomology.constantTransport (p := p) e he he' h).inv).comp
      (((Ext.mk₀ x).mapExactFunctor F).comp (Ext.mk₀ ((c).hom.f n)) (add_zero 0)) (zero_add 0) =
      Ext.mk₀ (transport p W A J δ base base' e he he' h a n x) :=
  ExtZero.ExtZeroTransport.mk F (NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistCohomology.constantTransport (p := p) e he he' h).inv
    ((c).hom.f n) x

theorem sections_apply (n : ℕ) (x : A₁ ⟶ (L).X n) (V : Cᵒᵖ) :
    (targetSections p W A J δ base a n (transport p W A J δ base base' e he he' h a n x)).app V (1 : R) =
      ((c).hom.f n).hom.app V
        ((sourceSections p W A J δ base' a n x).app ((ι).op.obj V) (1 : R)) := by
  have hs := congrArg (fun s => s.app V (1 : R))
    (sections p W A J δ base base' e he he' h a n x)
  change _ = ((c).hom.f n).hom.app V
    ((sourceSections p W A J δ base' a n x).app ((ι).op.obj V)
      ((NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistCohomology.coefficientEquiv e).symm (1 : R))) at hs
  simpa only [map_one] using hs

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.TwistSectionCoordinates.BigCrystallineTwistSectionCoordinates

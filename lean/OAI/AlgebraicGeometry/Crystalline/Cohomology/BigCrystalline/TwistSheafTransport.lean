import OAI.AlgebraicGeometry.Crystalline.Cohomology.TwistEquivalence
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.TwistPresheafSource
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameSheafResolution
import OAI.AlgebraicGeometry.Crystalline.Cohomology.ChangedCoefficient

/-! # Twist Sheaf Transport -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.TwistSheafTransport.BigCrystallineTwistSheafTransport

noncomputable section

/-! # The original coefficient-twisted restriction of the affine frame sheaf resolution -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Functor _root_.AlgebraicGeometry

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
local notation "ι" => OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineBaseTwist.twist (p := p) e he h
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite.Object.topology
  (p := p) (J := J) (δ := δ) (f := base)
local notation "U" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite.Object.topology
  (p := p) (J := J) (δ := δ) (f := base')
local notation "P" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.TwistResolution.BigCrystallineTwistResolution.restriction p W A J δ base base' e he h
local notation "L" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameSheafResolution.BigCrystallineFrameSheafResolution.coefficientLift W

def largeRestriction : ModuleCat.{u + 1} R ⥤ ModuleCat.{u + 1} R :=
  ModuleCat.restrictScalars (NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistCohomology.coefficientEquiv e).symm.toRingHom

local notation "Q" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.TwistSheafTransport.BigCrystallineTwistSheafTransport.largeRestriction W e

instance largeRestriction_hasSheafCompose : (T).HasSheafCompose Q :=
  inferInstanceAs ((T).HasSheafCompose
    (ModuleCat.restrictScalars (NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistCohomology.coefficientEquiv e).symm.toRingHom))

instance largeRestriction_preservesSheafification : (T).PreservesSheafification Q :=
  Sheaf.preservesSheafification_of_adjunction T
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{u + 1}
      (NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistCohomology.coefficientEquiv e).symm).toAdjunction

def liftedIso :
    (Functor.whiskeringRight Dᵒᵖ (ModuleCat W) (ModuleCat.{u + 1} R)).obj L ⋙
      (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (ModuleCat.{u + 1} R)).obj (ι).op ⋙
      (Functor.whiskeringRight Cᵒᵖ (ModuleCat.{u + 1} R) (ModuleCat.{u + 1} R)).obj Q ≅
    P ⋙ (Functor.whiskeringRight Cᵒᵖ (ModuleCat W) (ModuleCat.{u + 1} R)).obj L :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

abbrev restriction :=
  NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistCohomology.twistedRestriction (p := p) e he he' h

def comparisonIso : FrameSheafResolution.BigCrystallineFrameSheafResolution.toSheaf p W A J δ base' ⋙
    restriction p W A J δ base base' e he he' h ≅
      P ⋙ FrameSheafResolution.BigCrystallineFrameSheafResolution.toSheaf p W A J δ base :=
  by
    let := NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistRestriction.twist_continuous (p := p) e he he' h
    let := NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistRestriction.twist_cocontinuous (p := p) e he he' h
    exact isoWhiskerLeft
      ((Functor.whiskeringRight Dᵒᵖ (ModuleCat W) (ModuleCat.{u + 1} R)).obj L)
      (ChangedCoefficient.ChangedCoefficientSheafificationNaturality.iso T U (ι) Q) ≪≫
      isoWhiskerRight (liftedIso p W A J δ base base' e he h)
        (presheafToSheaf T (ModuleCat.{u + 1} R))

def structureIso : (restriction p W A J δ base base' e he he' h).obj
    (NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.structureSheaf (p := p) (J := J) (δ := δ) base') ≅
      NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.structureSheaf (p := p) (J := J) (δ := δ) base :=
  (comparisonIso p W A J δ base base' e he he' h).app
      (NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.modulePresheaf (p := p) (J := J) (δ := δ) base') ≪≫
    (FrameSheafResolution.BigCrystallineFrameSheafResolution.toSheaf p W A J δ base).mapIso
      (TwistPresheafSource.BigCrystallineTwistPresheafSource.iso p W A J δ base base' e he h)

theorem structureIso_original : structureIso p W A J δ base base' e he he' h =
    NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistCohomology.structureTransport (p := p) e he he' h := by
  let := NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistRestriction.twist_continuous (p := p) e he he' h
  let := NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistRestriction.twist_cocontinuous (p := p) e he he' h
  let G₀ := NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.modulePresheaf (p := p) (J := J) (δ := δ) base'
  let S := presheafToSheaf T (ModuleCat.{u + 1} R)
  let i := NumberTheory.PadicHodge.PeriodInvariants.ChangedCoefficientSheafification.transport T U (ι) Q (G₀ ⋙ L)
  let c := (liftedIso p W A J δ base base' e he h).hom.app G₀
  let d := Functor.whiskerRight
    (TwistPresheafSource.BigCrystallineTwistPresheafSource.iso p W A J δ base base' e he h).hom L
  let b := NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistCohomology.presheafTransport (p := p) e he h
  have hc : c ≫ d = b.hom := by ext V x; rfl
  apply Iso.ext
  change (i.hom ≫ S.map c) ≫ S.map d = i.hom ≫ S.map b.hom
  exact (Category.assoc i.hom (S.map c) (S.map d)).trans
    (congrArg (fun t => i.hom ≫ t) ((S.map_comp c d).symm.trans (congrArg S.map hc)))

variable {σ : Type u} (a : σ → A) [Fintype σ] [LinearOrder σ]

def complexIso : ((restriction p W A J δ base base' e he he' h).mapHomologicalComplex (.up ℕ)).obj
    (FrameSheafResolution.BigCrystallineFrameSheafResolution.complex p W A J δ base' a) ≅
      FrameSheafResolution.BigCrystallineFrameSheafResolution.complex p W A J δ base a :=
  (Functor.mapHomologicalComplexCompIso
      (comparisonIso p W A J δ base base' e he he' h) (.up ℕ)).app
      (FrameResolution.BigCrystallineFrameResolution.complex (p := p) (J := J) (δ := δ) (base := base') a) ≪≫
    ((FrameSheafResolution.BigCrystallineFrameSheafResolution.toSheaf p W A J δ base).mapHomologicalComplex (.up ℕ)).mapIso
      (TwistResolution.BigCrystallineTwistResolution.iso p W A J δ base base' e he h a)

theorem component (n : ℕ) : (complexIso p W A J δ base base' e he he' h a).hom.f n =
    (comparisonIso p W A J δ base base' e he he' h).hom.app
        ((FrameResolution.BigCrystallineFrameResolution.complex (p := p) (J := J) (δ := δ) (base := base') a).X n) ≫
      (FrameSheafResolution.BigCrystallineFrameSheafResolution.toSheaf p W A J δ base).map
        ((TwistResolution.BigCrystallineTwistResolution.iso p W A J δ base base' e he h a).hom.f n) := rfl

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.TwistSheafTransport.BigCrystallineTwistSheafTransport

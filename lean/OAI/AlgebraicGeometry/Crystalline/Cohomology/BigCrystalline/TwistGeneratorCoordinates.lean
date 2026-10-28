import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.TwistSheafTransport
import OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafificationMap
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Module.ScalarSquareEvaluation

/-! # Twist Generator Coordinates -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.TwistGeneratorCoordinates.BigCrystallineTwistGeneratorCoordinates

noncomputable section

/-! # The original crystalline twist comparison on actual frame generators -/

open _root_.CategoryTheory _root_.CategoryTheory.Functor _root_.AlgebraicGeometry

universe u

variable (p : ℕ) (W A : Type u) [CommRing W] [CommRing A]
  (J : Ideal W) (δ : DividedPowers J)
  (base base' : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of W))
  (e : W ≃+* W) (he : DividedPowers.IsDPMorphism δ δ e.toRingHom)
  (he' : DividedPowers.IsDPMorphism δ δ e.symm.toRingHom)
  (h : base' = base ≫ Spec.map (CommRingCat.ofHom e.toRingHom))
  {σ : Type u} (a : σ → A) [Fintype σ] [LinearOrder σ]

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := W)
local notation "ι" => OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineBaseTwist.twist (p := p) e he h
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite.Object.topology
  (p := p) (J := J) (δ := δ) (f := base)
local notation "U" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite.Object.topology
  (p := p) (J := J) (δ := δ) (f := base')
local notation "E" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameSheafResolution.BigCrystallineFrameSheafResolution.coefficientLift W
local notation "Q" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.TwistSheafTransport.BigCrystallineTwistSheafTransport.largeRestriction W e

def sourcePresheaf (n : ℕ) :=
  (FrameResolution.BigCrystallineFrameResolution.complex (p := p) (J := J) (δ := δ) (base := base') a).X n ⋙ E

def targetPresheaf (n : ℕ) :=
  (FrameResolution.BigCrystallineFrameResolution.complex (p := p) (J := J) (δ := δ) (base := base) a).X n ⋙ E

def rawMap (n : ℕ) :
    ((ι).op ⋙ sourcePresheaf p W A J δ base' a n) ⋙ Q ⟶
      targetPresheaf p W A J δ base a n :=
  (TwistSheafTransport.BigCrystallineTwistSheafTransport.liftedIso p W A J δ base base' e he h).hom.app
      ((FrameResolution.BigCrystallineFrameResolution.complex (p := p) (J := J) (δ := δ) (base := base') a).X n) ≫
    whiskerRight ((TwistResolution.BigCrystallineTwistResolution.iso p W A J δ base base' e he h a).hom.f n) E

theorem component (n : ℕ) :
    letI := NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistRestriction.twist_continuous (p := p) e he he' h
    letI := NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistRestriction.twist_cocontinuous (p := p) e he he' h
    ((TwistSheafTransport.BigCrystallineTwistSheafTransport.complexIso p W A J δ base base' e he he' h a).hom.f n).hom =
      (NumberTheory.PadicHodge.PeriodInvariants.ChangedCoefficientSheafification.transport T U ι Q
        (sourcePresheaf p W A J δ base' a n)).hom.hom ≫
          sheafifyMap T (rawMap p W A J δ base base' e he h a n) := by
  let := NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistRestriction.twist_continuous (p := p) e he he' h
  let := NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistRestriction.twist_cocontinuous (p := p) e he he' h
  let S := presheafToSheaf T (ModuleCat.{u + 1} R)
  let i := NumberTheory.PadicHodge.PeriodInvariants.ChangedCoefficientSheafification.transport T U ι Q
    (sourcePresheaf p W A J δ base' a n)
  let c := (TwistSheafTransport.BigCrystallineTwistSheafTransport.liftedIso p W A J δ base base' e he h).hom.app
    ((FrameResolution.BigCrystallineFrameResolution.complex (p := p) (J := J) (δ := δ) (base := base') a).X n)
  let d := whiskerRight ((TwistResolution.BigCrystallineTwistResolution.iso p W A J δ base base' e he h a).hom.f n) E
  have hm : (i.hom ≫ S.map c) ≫ S.map d = i.hom ≫ S.map (c ≫ d) :=
    (Category.assoc _ _ _).trans (congrArg (fun t => i.hom ≫ t) (S.map_comp c d).symm)
  exact congrArg (fun t => t.hom) hm

theorem generator (n : ℕ) :
    whiskerRight (whiskerLeft (ι).op (toSheafify U (sourcePresheaf p W A J δ base' a n))) Q ≫
      ((TwistSheafTransport.BigCrystallineTwistSheafTransport.complexIso p W A J δ base base' e he he' h a).hom.f n).hom =
    rawMap p W A J δ base base' e he h a n ≫
      toSheafify T (targetPresheaf p W A J δ base a n) := by
  let := NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistRestriction.twist_continuous (p := p) e he he' h
  let := NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistRestriction.twist_cocontinuous (p := p) e he he' h
  exact (congrArg (fun t =>
    whiskerRight (whiskerLeft (ι).op (toSheafify U (sourcePresheaf p W A J δ base' a n))) Q ≫ t)
      (component p W A J δ base base' e he he' h a n)).trans
    (SheafificationMap.SheafificationMapGenerators.changed_generator T U ι Q
      (sourcePresheaf p W A J δ base' a n) (targetPresheaf p W A J δ base a n)
      (rawMap p W A J δ base base' e he h a n))

theorem generator_apply (n : ℕ)
    (V : (FrameLifts.BigCrystallineFrameLifts.Site p W A J δ base)ᵒᵖ)
    (z : (sourcePresheaf p W A J δ base' a n).obj ((ι).op.obj V)) :
    ScalarRestricted.ScalarRestrictedAdditiveMap.map
      (NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistCohomology.coefficientEquiv e).symm.toRingHom
      (((TwistSheafTransport.BigCrystallineTwistSheafTransport.complexIso p W A J δ base base' e he he' h a).hom.f n).hom.app V)
      ((toSheafify U (sourcePresheaf p W A J δ base' a n)).app ((ι).op.obj V) z) =
    (toSheafify T (targetPresheaf p W A J δ base a n)).app V
      (ScalarRestricted.ScalarRestrictedAdditiveMap.map
        (NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistCohomology.coefficientEquiv e).symm.toRingHom
        ((rawMap p W A J δ base base' e he h a n).app V) z) := by
  have hs := congrArg (fun f => f.app V) (generator p W A J δ base base' e he he' h a n)
  have ha := Module.ScalarSquareEvaluation.ModuleScalarSquareEvaluation.addHom
    (NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistCohomology.coefficientEquiv e).symm.toRingHom
    ((toSheafify U (sourcePresheaf p W A J δ base' a n)).app ((ι).op.obj V))
    ((rawMap p W A J δ base base' e he h a n).app V)
    ((toSheafify T (targetPresheaf p W A J δ base a n)).app V)
    (((TwistSheafTransport.BigCrystallineTwistSheafTransport.complexIso p W A J δ base base' e he he' h a).hom.f n).hom.app V)
    hs.symm
  exact (DFunLike.congr_fun ha z).symm

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.TwistGeneratorCoordinates.BigCrystallineTwistGeneratorCoordinates

import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.TwistPresheafSource
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.RelativeAugmentation
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Mapped.AugmentationZero

/-! # Twist Augmentation -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.TwistAugmentation.BigCrystallineTwistAugmentation

noncomputable section

/-! # Base twist preserves the original affine frame augmentation -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameLifts.BigCrystallineFrameLifts

universe u

variable (p : ℕ) (W A : Type u) [CommRing W] [CommRing A]
  (J : Ideal W) (δ : DividedPowers J)
  (base base' : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of W))
  (e : W ≃+* W) (he : DividedPowers.IsDPMorphism δ δ e.toRingHom)
  (h : base' = base ≫ Spec.map (CommRingCat.ofHom e.toRingHom))

local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameLifts.BigCrystallineFrameLifts.Site p W A J δ base
local notation "ι" => OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineBaseTwist.twist (p := p) e he h
local notation "F" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.TwistResolution.BigCrystallineTwistResolution.restriction p W A J δ base base' e he h
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.modulePresheaf
  (p := p) (J := J) (δ := δ) base'
local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.modulePresheaf
  (p := p) (J := J) (δ := δ) base

abbrev sourceIso := TwistPresheafSource.BigCrystallineTwistPresheafSource.iso p W A J δ base base' e he h

variable {σ : Type u} (a : σ → A) [Fintype σ] [LinearOrder σ]

local notation "α" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameResolution.BigCrystallineFrameResolution.augmentation
  (p := p) (J := J) (δ := δ) (base := base') a
local notation "β" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameResolution.BigCrystallineFrameResolution.augmentation
  (p := p) (J := J) (δ := δ) (base := base) a

abbrev Form (Q : Cᵒᵖ) :=
  PD.DeRham.PDDeRham.Form Q.unop.ring (DividedPowerAlgebra Q.unop.ring (σ →₀ Q.unop.ring))
    (Multivariable.DividedPowers.MultivariableDividedPowers.ideal Q.unop.ring σ Q.unop.ideal)
    (FreeRelative.Powers.FreeRelativePowers.dividedPowers Q.unop.ring σ Q.unop.ideal Q.unop.dividedPowers) 0

def sourceValue (Q : Cᵒᵖ) (x : Q.unop.ring) : Form p W A J δ base (σ := σ) Q :=
  ((((RelativeAugmentation.BigCrystallineRelativeAugmentation.augmentation
    (p := p) (J := J) (δ := δ) (base := base') a).f 0).app ((ι).op.obj Q)).hom x)

def targetValue (Q : Cᵒᵖ) (x : Q.unop.ring) : Form p W A J δ base (σ := σ) Q :=
  ((((RelativeAugmentation.BigCrystallineRelativeAugmentation.augmentation
    (p := p) (J := J) (δ := δ) (base := base) a).f 0).app Q)).hom x

def symbolValue (Q : Cᵒᵖ) (x : Q.unop.ring) : Form p W A J δ base (σ := σ) Q :=
  PD.DeRham.PDDeRham.symbol Q.unop.ring (DividedPowerAlgebra Q.unop.ring (σ →₀ Q.unop.ring))
    (Multivariable.DividedPowers.MultivariableDividedPowers.ideal Q.unop.ring σ Q.unop.ideal)
    (FreeRelative.Powers.FreeRelativePowers.dividedPowers Q.unop.ring σ Q.unop.ideal Q.unop.dividedPowers)
    (algebraMap Q.unop.ring (DividedPowerAlgebra Q.unop.ring (σ →₀ Q.unop.ring)) x) Fin.elim0

theorem sourceValue_eq (Q : Cᵒᵖ) (x : Q.unop.ring) :
    sourceValue p W A J δ base base' e he h a Q x = symbolValue p W A J δ base (σ := σ) Q x :=
  RelativeAugmentation.BigCrystallineRelativeAugmentation.zero a ((ι).op.obj Q) x

theorem targetValue_eq (Q : Cᵒᵖ) (x : Q.unop.ring) :
    targetValue p W A J δ base a Q x = symbolValue p W A J δ base (σ := σ) Q x :=
  RelativeAugmentation.BigCrystallineRelativeAugmentation.zero a Q x

theorem relative_zero (Q : Cᵒᵖ) (x : Q.unop.ring) :
    (show Form p W A J δ base (σ := σ) Q from
      (((TwistResolution.BigCrystallineTwistResolution.relativeIso p W A J δ base base' e he h a).hom.f 0).app Q).hom
        (sourceValue p W A J δ base base' e he h a Q x)) = targetValue p W A J δ base a Q x := by
  have hi := TwistResolution.BigCrystallineTwistResolution.relative_apply p W A J δ base base' e he h a Q 0
    (sourceValue p W A J δ base base' e he h a Q x)
  exact hi.trans ((sourceValue_eq p W A J δ base base' e he h a Q x).trans
    (targetValue_eq p W A J δ base a Q x).symm)

theorem relative :
    (HomologicalComplex.singleMapHomologicalComplex F (.up ℕ) 0).inv.app G ≫
        ((F).mapHomologicalComplex (.up ℕ)).map
          (RelativeAugmentation.BigCrystallineRelativeAugmentation.augmentation
            (p := p) (J := J) (δ := δ) (base := base') a) ≫
        (TwistResolution.BigCrystallineTwistResolution.relativeIso p W A J δ base base' e he h a).hom =
      (CochainComplex.single₀ _).map (sourceIso p W A J δ base base' e he h).hom ≫
        RelativeAugmentation.BigCrystallineRelativeAugmentation.augmentation
          (p := p) (J := J) (δ := δ) (base := base) a := by
  apply HomologicalComplex.from_single_hom_ext
  rw [← Category.assoc, HomologicalComplex.comp_f, Mapped.AugmentationZero.MappedAugmentationZero.mapped,
    HomologicalComplex.comp_f, CochainComplex.single₀_map_f_zero]
  apply NatTrans.ext
  funext Q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change Q.unop.ring at x
  exact relative_zero p W A J δ base base' e he h a Q x

theorem original :
    (HomologicalComplex.singleMapHomologicalComplex F (.up ℕ) 0).inv.app G ≫
        ((F).mapHomologicalComplex (.up ℕ)).map α ≫
        (TwistResolution.BigCrystallineTwistResolution.iso p W A J δ base base' e he h a).hom =
      (CochainComplex.single₀ _).map (sourceIso p W A J δ base base' e he h).hom ≫ β := by
  let t := RelativeForms.BigCrystallineRelativeForms.complexIso
    (p := p) (J := J) (δ := δ) (base := base) a
  let Z := (CochainComplex.single₀ (Cᵒᵖ ⥤ ModuleCat.{u} W)).obj ((F).obj G)
  have hr := congrArg (fun z : Z ⟶ RelativeForms.BigCrystallineRelativeForms.complex
      (p := p) (J := J) (δ := δ) (base := base) a => z ≫ t.inv)
    (relative p W A J δ base base' e he h a)
  simpa only [TwistResolution.BigCrystallineTwistResolution.iso, RelativeAugmentation.BigCrystallineRelativeAugmentation.augmentation,
    Functor.map_comp, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id, Category.comp_id, t] using hr

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.TwistAugmentation.BigCrystallineTwistAugmentation

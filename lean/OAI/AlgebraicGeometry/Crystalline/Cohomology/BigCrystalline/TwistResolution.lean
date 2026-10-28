import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.TwistRelativeForms
import OAI.AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyTrans

/-! # Twist Resolution -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.TwistResolution.BigCrystallineTwistResolution

noncomputable section

/-! # The original affine frame resolution under inverse scalar base twist -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameLifts.BigCrystallineFrameLifts

universe u

variable (p : ℕ) (W A : Type u) [CommRing W] [CommRing A]
  (J : Ideal W) (δ : DividedPowers J)
  (base base' : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of W))
  (e : W ≃+* W) (he : DividedPowers.IsDPMorphism δ δ e.toRingHom)
  (h : base' = base ≫ Spec.map (CommRingCat.ofHom e.toRingHom))

local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameLifts.BigCrystallineFrameLifts.Site p W A J δ base
local notation "D" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameLifts.BigCrystallineFrameLifts.Site p W A J δ base'
local notation "ι" => OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineBaseTwist.twist (p := p) e he h

def restriction : (Dᵒᵖ ⥤ ModuleCat W) ⥤ (Cᵒᵖ ⥤ ModuleCat W) :=
  (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (ModuleCat W)).obj (ι).op ⋙
    (Functor.whiskeringRight Cᵒᵖ (ModuleCat W) (ModuleCat W)).obj
      (ModuleCat.restrictScalars e.symm.toRingHom)

instance restriction_additive : (restriction p W A J δ base base' e he h).Additive := by
  unfold restriction
  infer_instance

variable {σ : Type u} (a : σ → A) [Fintype σ] [LinearOrder σ]

local notation "F" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.TwistResolution.BigCrystallineTwistResolution.restriction p W A J δ base base' e he h

def assemblyIso : ((F).mapHomologicalComplex (.up ℕ)).obj
    (RelativeForms.BigCrystallineRelativeForms.complex (p := p) (J := J) (δ := δ) (base := base') a) ≅
      ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ)
        (TwistRelativeForms.BigCrystallineTwistRelativeForms.twistedFunctor p W A σ J δ base base' e he h a) :=
  ComplexAssemblyTrans.ComplexAssemblyTransport.iso (ι).op (ModuleCat.restrictScalars e.symm.toRingHom) (.up ℕ)
    (RelativeForms.BigCrystallineRelativeForms.functor (p := p) (J := J) (δ := δ) (base := base') a)

def relativeIso : ((F).mapHomologicalComplex (.up ℕ)).obj
    (RelativeForms.BigCrystallineRelativeForms.complex (p := p) (J := J) (δ := δ) (base := base') a) ≅
      RelativeForms.BigCrystallineRelativeForms.complex (p := p) (J := J) (δ := δ) (base := base) a :=
  assemblyIso p W A J δ base base' e he h a ≪≫
    (ComplexAssemblyQuasi.ComplexAssembly.functor (.up ℕ)).mapIso
      (TwistRelativeForms.BigCrystallineTwistRelativeForms.iso p W A σ J δ base base' e he h a)

def iso : ((F).mapHomologicalComplex (.up ℕ)).obj
    (FrameResolution.BigCrystallineFrameResolution.complex (p := p) (J := J) (δ := δ) (base := base') a) ≅
      FrameResolution.BigCrystallineFrameResolution.complex (p := p) (J := J) (δ := δ) (base := base) a :=
  ((F).mapHomologicalComplex (.up ℕ)).mapIso
      (RelativeForms.BigCrystallineRelativeForms.complexIso (p := p) (J := J) (δ := δ) (base := base') a) ≪≫
    relativeIso p W A J δ base base' e he h a ≪≫
      (RelativeForms.BigCrystallineRelativeForms.complexIso (p := p) (J := J) (δ := δ) (base := base) a).symm

theorem relative_component (Q : Cᵒᵖ) (n : ℕ) :
    ((relativeIso p W A J δ base base' e he h a).hom.f n).app Q =
      ((TwistRelativeForms.BigCrystallineTwistRelativeForms.objectIso p W A σ J δ base base' e he h a Q).hom.f n) :=
  ComplexAssemblyTrans.ComplexAssemblyTransport.iso_trans_component (ι).op
    (ModuleCat.restrictScalars e.symm.toRingHom) (.up ℕ)
    (RelativeForms.BigCrystallineRelativeForms.functor (p := p) (J := J) (δ := δ) (base := base') a)
    (RelativeForms.BigCrystallineRelativeForms.functor (p := p) (J := J) (δ := δ) (base := base) a)
    (TwistRelativeForms.BigCrystallineTwistRelativeForms.iso p W A σ J δ base base' e he h a) n Q

theorem object_apply (Q : Cᵒᵖ) (n : ℕ)
    (x : PD.DeRham.PDDeRham.Form Q.unop.ring (DividedPowerAlgebra Q.unop.ring (σ →₀ Q.unop.ring))
      (Multivariable.DividedPowers.MultivariableDividedPowers.ideal Q.unop.ring σ Q.unop.ideal)
      (FreeRelative.Powers.FreeRelativePowers.dividedPowers Q.unop.ring σ Q.unop.ideal Q.unop.dividedPowers) n) :
    ((TwistRelativeForms.BigCrystallineTwistRelativeForms.objectIso p W A σ J δ base base' e he h a Q).hom.f n).hom x = x :=
  InverseTwist.InverseTwistScalarRestriction.component Q.unop.base e
    (PD.DeRham.PDDeRham.complex Q.unop.ring (DividedPowerAlgebra Q.unop.ring (σ →₀ Q.unop.ring))
      (Multivariable.DividedPowers.MultivariableDividedPowers.ideal Q.unop.ring σ Q.unop.ideal)
      (FreeRelative.Powers.FreeRelativePowers.dividedPowers Q.unop.ring σ Q.unop.ideal Q.unop.dividedPowers)) n x

theorem relative_apply (Q : Cᵒᵖ) (n : ℕ)
    (x : PD.DeRham.PDDeRham.Form Q.unop.ring (DividedPowerAlgebra Q.unop.ring (σ →₀ Q.unop.ring))
      (Multivariable.DividedPowers.MultivariableDividedPowers.ideal Q.unop.ring σ Q.unop.ideal)
      (FreeRelative.Powers.FreeRelativePowers.dividedPowers Q.unop.ring σ Q.unop.ideal Q.unop.dividedPowers) n) :
    (((relativeIso p W A J δ base base' e he h a).hom.f n).app Q).hom x = x := by
  let M := ((TwistRelativeForms.BigCrystallineTwistRelativeForms.twistedFunctor p W A σ J δ base base' e he h a).obj Q).X n
  let N := (RelativeForms.BigCrystallineRelativeForms.object (σ := σ) Q).X n
  have hc := congrArg (fun f : M ⟶ N => f.hom x)
    (relative_component p W A J δ base base' e he h a Q n)
  exact hc.trans (object_apply p W A J δ base base' e he h a Q n x)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.TwistResolution.BigCrystallineTwistResolution

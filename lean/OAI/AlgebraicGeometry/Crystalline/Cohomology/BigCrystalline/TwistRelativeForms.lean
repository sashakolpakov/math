import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.TwistLifts
import OAI.AlgebraicGeometry.Crystalline.Cohomology.InverseTwist
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.RelativeForms

/-! # Twist Relative Forms -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.TwistRelativeForms.BigCrystallineTwistRelativeForms

noncomputable section

/-! # Relative frame forms under the original crystalline base twist -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameLifts.BigCrystallineFrameLifts

universe u

variable (p : ℕ) (W A σ : Type u) [CommRing W] [CommRing A]
  (J : Ideal W) (δ : DividedPowers J)
  (base base' : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of W))
  (e : W ≃+* W) (he : DividedPowers.IsDPMorphism δ δ e.toRingHom)
  (h : base' = base ≫ Spec.map (CommRingCat.ofHom e.toRingHom))
  (a : σ → A) [Fintype σ] [LinearOrder σ]

local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameLifts.BigCrystallineFrameLifts.Site p W A J δ base
local notation "ι" => OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineBaseTwist.twist (p := p) e he h

def twistedFunctor : Cᵒᵖ ⥤ CochainComplex (ModuleCat W) ℕ :=
  (ι).op ⋙ RelativeForms.BigCrystallineRelativeForms.functor (p := p) (J := J) (δ := δ) (base := base') a ⋙
    (ModuleCat.restrictScalars e.symm.toRingHom).mapHomologicalComplex (.up ℕ)

def objectIso (Q : Cᵒᵖ) : (twistedFunctor p W A σ J δ base base' e he h a).obj Q ≅
    (RelativeForms.BigCrystallineRelativeForms.functor (p := p) (J := J) (δ := δ) (base := base) a).obj Q :=
  InverseTwist.InverseTwistScalarRestriction.complexIso Q.unop.base e
    (PD.DeRham.PDDeRham.complex Q.unop.ring (DividedPowerAlgebra Q.unop.ring (σ →₀ Q.unop.ring))
      (Multivariable.DividedPowers.MultivariableDividedPowers.ideal Q.unop.ring σ Q.unop.ideal)
      (FreeRelative.Powers.FreeRelativePowers.dividedPowers Q.unop.ring σ Q.unop.ideal Q.unop.dividedPowers))

def iso : twistedFunctor p W A σ J δ base base' e he h a ≅
    RelativeForms.BigCrystallineRelativeForms.functor (p := p) (J := J) (δ := δ) (base := base) a :=
  NatIso.ofComponents (objectIso p W A σ J δ base base' e he h a) (by
    intro Q P f
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.TwistRelativeForms.BigCrystallineTwistRelativeForms

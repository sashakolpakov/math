import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.PowerCoordinates
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.RelativeForms
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.RelativeScalarSquare

/-! # Power Forms -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.PowerForms.BigCrystallinePowerForms

noncomputable section

/-! # Actual power-coordinate maps of big crystalline frame complexes -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameLifts.BigCrystallineFrameLifts OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.PowerCoordinates.BigCrystallinePowerCoordinates

universe u

variable {p : ℕ} {W A σ : Type u} [CommRing W] [CommRing A]
  {J : Ideal W} {δ : DividedPowers J} {base : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of W)}
  (a : σ → A) (m : ℕ) [Fintype σ] [LinearOrder σ]

local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameLifts.BigCrystallineFrameLifts.Site p W A J δ base

def ambientMap (Q : C) : DividedPowerAlgebra Q.ring (σ →₀ Q.ring) →ₐ[Q.ring]
    DividedPowerAlgebra Q.ring (σ →₀ Q.ring) :=
  FreeRelative.PowerMap.FreeRelativePowerMap.map Q.ring σ Q.ideal Q.dividedPowers m
    (PowerCoordinates.BigCrystallinePowerCoordinates.targetLift a Q) (PowerCoordinates.BigCrystallinePowerCoordinates.sourceLift a m Q) (PowerCoordinates.BigCrystallinePowerCoordinates.power_difference_mem a m Q)

def component (Q : Cᵒᵖ) : RelativeForms.BigCrystallineRelativeForms.object (σ := σ) Q ⟶
    RelativeForms.BigCrystallineRelativeForms.object (σ := σ) Q :=
  PD.RelativeScalarSquare.PDRelativeScalarSquare.selfMap W Q.unop.ring (DividedPowerAlgebra Q.unop.ring (σ →₀ Q.unop.ring))
    (Multivariable.DividedPowers.MultivariableDividedPowers.ideal Q.unop.ring σ Q.unop.ideal)
    (FreeRelative.Powers.FreeRelativePowers.dividedPowers Q.unop.ring σ Q.unop.ideal Q.unop.dividedPowers)
    (ambientMap a m Q.unop) (PowerCoordinates.BigCrystallinePowerCoordinates.map_isDPMorphism a m Q.unop)

omit [Fintype σ] [LinearOrder σ] in
theorem naturality {Q P : Cᵒᵖ} (f : Q ⟶ P) :
    RelativeForms.BigCrystallineRelativeForms.map (fun i => a i ^ m) f ≫ component a m P =
      component a m Q ≫ RelativeForms.BigCrystallineRelativeForms.map a f := by
  exact (PD.RelativeScalarSquare.PDRelativeScalarSquare.square W Q.unop.ring P.unop.ring
    (DividedPowerAlgebra Q.unop.ring (σ →₀ Q.unop.ring))
    (DividedPowerAlgebra P.unop.ring (σ →₀ P.unop.ring))
    (Multivariable.DividedPowers.MultivariableDividedPowers.ideal Q.unop.ring σ Q.unop.ideal)
    (FreeRelative.Powers.FreeRelativePowers.dividedPowers Q.unop.ring σ Q.unop.ideal Q.unop.dividedPowers)
    (Multivariable.DividedPowers.MultivariableDividedPowers.ideal P.unop.ring σ P.unop.ideal)
    (FreeRelative.Powers.FreeRelativePowers.dividedPowers P.unop.ring σ P.unop.ideal P.unop.dividedPowers)
    f.unop.ringMap.toRingHom (fun w => DFunLike.congr_fun f.unop.overBase w)
    (FrameMaps.BigCrystallineFrameMaps.ambientMap (fun i => a i ^ m) f.unop).toRingHom
    (FrameMaps.BigCrystallineFrameMaps.ambientMap a f.unop).toRingHom
    (FrameMaps.BigCrystallineFrameMaps.ambientMap_coefficient (fun i => a i ^ m) f.unop)
    (FrameMaps.BigCrystallineFrameMaps.ambientMap_coefficient a f.unop)
    (FrameMaps.BigCrystallineFrameMaps.ambientMap_relativePD (fun i => a i ^ m) f.unop)
    (FrameMaps.BigCrystallineFrameMaps.ambientMap_relativePD a f.unop)
    (ambientMap a m Q.unop) (ambientMap a m P.unop)
    (PowerCoordinates.BigCrystallinePowerCoordinates.map_isDPMorphism a m Q.unop) (PowerCoordinates.BigCrystallinePowerCoordinates.map_isDPMorphism a m P.unop)
    (PowerCoordinates.BigCrystallinePowerCoordinates.naturality a m f.unop)).symm

def transformation : RelativeForms.BigCrystallineRelativeForms.functor (p := p) (J := J) (δ := δ) (base := base)
    (fun i => a i ^ m) ⟶ RelativeForms.BigCrystallineRelativeForms.functor a where
  app := component a m
  naturality _ _ f := BigCrystallinePowerForms.naturality a m f

def relativeComplexMap : RelativeForms.BigCrystallineRelativeForms.complex (p := p) (J := J) (δ := δ) (base := base)
    (fun i => a i ^ m) ⟶ RelativeForms.BigCrystallineRelativeForms.complex a :=
  ComplexAssemblyQuasi.ComplexAssembly.map (.up ℕ) (transformation a m)

def complexMap : FrameResolution.BigCrystallineFrameResolution.complex (p := p) (J := J) (δ := δ) (base := base)
    (fun i => a i ^ m) ⟶ FrameResolution.BigCrystallineFrameResolution.complex a :=
  (RelativeForms.BigCrystallineRelativeForms.complexIso (fun i => a i ^ m)).hom ≫
    relativeComplexMap a m ≫ (RelativeForms.BigCrystallineRelativeForms.complexIso a).inv

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.PowerForms.BigCrystallinePowerForms

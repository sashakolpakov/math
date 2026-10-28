import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.PullbackAugmentation
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameSheafResolution

/-! # Pullback Sheaf Transport -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.PullbackSheafTransport.BigCrystallinePullbackSheafTransport

noncomputable section

/-! # Exact geometric pullback of the original affine frame sheaf resolution -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable (p : ℕ) (W A B : Type u) [CommRing W] [CommRing A] [CommRing B]
  (J : Ideal W) (δ : DividedPowers J) (base : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of W))
  (φ : B →+* A)

local notation "g" => Spec.map (CommRingCat.ofHom φ)
local notation "bA" => g ≫ base
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := W)
local notation "ι" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.PullbackLifts.BigCrystallinePullbackLifts.postcompose p W A B J δ base φ
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite.Object.topology (p := p) (B := W)
  (J := J) (δ := δ) (f := bA)
local notation "U" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite.Object.topology (p := p) (B := W)
  (J := J) (δ := δ) (f := base)

instance postcompose_continuous : (ι).IsContinuous T U :=
  inferInstanceAs ((NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite.postcompose g rfl).IsContinuous T U)

instance postcompose_cocontinuous : (ι).IsCocontinuous T U :=
  inferInstanceAs ((NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite.postcompose g rfl).IsCocontinuous T U)

abbrev restriction := NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.restriction
  (p := p) (J := J) (δ := δ) (fY := base) g rfl

def comparisonIso : FrameSheafResolution.BigCrystallineFrameSheafResolution.toSheaf p W B J δ base ⋙
    restriction p W A B J δ base φ ≅
      PullbackResolution.BigCrystallinePullbackResolution.restriction p W A B J δ base φ ⋙
        FrameSheafResolution.BigCrystallineFrameSheafResolution.toSheaf p W A J δ bA :=
  NatIso.ofComponents (fun P =>
    ((ι).pushforwardContinuousSheafificationCompatibility (ModuleCat.{u + 1} R) T U).symm.app
      (P ⋙ FrameSheafResolution.BigCrystallineFrameSheafResolution.coefficientLift W)) (by
    intro P Q f
    exact ((ι).pushforwardContinuousSheafificationCompatibility (ModuleCat.{u + 1} R) T U).inv.naturality
      (Functor.whiskerRight f (FrameSheafResolution.BigCrystallineFrameSheafResolution.coefficientLift W)))

def structureIso : (restriction p W A B J δ base φ).obj
    (NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.structureSheaf (p := p) (J := J) (δ := δ) base) ≅
      NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.structureSheaf (p := p) (J := J) (δ := δ) bA :=
  (comparisonIso p W A B J δ base φ).app
      (NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.modulePresheaf (p := p) (J := J) (δ := δ) base) ≪≫
    (FrameSheafResolution.BigCrystallineFrameSheafResolution.toSheaf p W A J δ bA).mapIso
      (PullbackAugmentation.BigCrystallinePullbackAugmentation.sourceIso p W A B J δ base φ)

theorem structureIso_original : structureIso p W A B J δ base φ =
    NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.structureTransport (p := p) (J := J) (δ := δ)
      (fY := base) g rfl := by
  apply Iso.ext
  rfl

variable {σ : Type u} (a : σ → B) [Fintype σ]

def complexIso : ((restriction p W A B J δ base φ).mapHomologicalComplex (.up ℕ)).obj
    (FrameSheafResolution.BigCrystallineFrameSheafResolution.complex p W B J δ base a) ≅
      FrameSheafResolution.BigCrystallineFrameSheafResolution.complex p W A J δ bA (φ ∘ a) :=
  (Functor.mapHomologicalComplexCompIso (comparisonIso p W A B J δ base φ) (.up ℕ)).app
      (FrameResolution.BigCrystallineFrameResolution.complex (p := p) (J := J) (δ := δ) (base := base) a) ≪≫
    ((FrameSheafResolution.BigCrystallineFrameSheafResolution.toSheaf p W A J δ bA).mapHomologicalComplex (.up ℕ)).mapIso
      (PullbackResolution.BigCrystallinePullbackResolution.iso p W A B σ J δ base φ a)

theorem component (n : ℕ) : (complexIso p W A B J δ base φ a).hom.f n =
    (comparisonIso p W A B J δ base φ).hom.app
        ((FrameResolution.BigCrystallineFrameResolution.complex (p := p) (J := J) (δ := δ) (base := base) a).X n) ≫
      (FrameSheafResolution.BigCrystallineFrameSheafResolution.toSheaf p W A J δ bA).map
        ((PullbackResolution.BigCrystallinePullbackResolution.iso p W A B σ J δ base φ a).hom.f n) := rfl

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.PullbackSheafTransport.BigCrystallinePullbackSheafTransport

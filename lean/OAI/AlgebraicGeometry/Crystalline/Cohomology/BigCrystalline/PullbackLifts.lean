import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameLifts

/-! # Pullback Lifts -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.PullbackLifts.BigCrystallinePullbackLifts

noncomputable section

/-! # The original chosen affine frame lifts under geometric pullback -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameLifts.BigCrystallineFrameLifts

universe u

variable (p : ℕ) (W A B σ : Type u) [CommRing W] [CommRing A] [CommRing B]
  (J : Ideal W) (δ : DividedPowers J) (base : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of W))
  (φ : B →+* A) (a : σ → B)

local notation "g" => Spec.map (CommRingCat.ofHom φ)
local notation "bA" => g ≫ base
local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameLifts.BigCrystallineFrameLifts.Site p W A J δ bA

def postcompose : C ⥤ FrameLifts.BigCrystallineFrameLifts.Site p W B J δ base :=
  NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite.postcompose g rfl

def pulledResidual (Q : C) : B →+* Q.ring ⧸ Q.ideal :=
  FrameLifts.BigCrystallineFrameLifts.residualMap p W B J δ base ((postcompose p W A B J δ base φ).obj Q)

theorem pulledResidual_spec (Q : C) :
    Spec.map (CommRingCat.ofHom (pulledResidual p W A B J δ base φ Q)) = Q.mapToX ≫ g :=
  FrameLifts.BigCrystallineFrameLifts.residualMap_spec p W B J δ base ((postcompose p W A B J δ base φ).obj Q)

theorem residual (Q : C) :
    FrameLifts.BigCrystallineFrameLifts.residualMap p W B J δ base ((postcompose p W A B J δ base φ).obj Q) =
      (FrameLifts.BigCrystallineFrameLifts.residualMap p W A J δ bA Q).comp φ := by
  have he : CommRingCat.ofHom (pulledResidual p W A B J δ base φ Q) =
      CommRingCat.ofHom φ ≫ CommRingCat.ofHom (FrameLifts.BigCrystallineFrameLifts.residualMap p W A J δ bA Q) := by
    apply Spec.map_injective
    rw [Spec.map_comp, pulledResidual_spec, FrameLifts.BigCrystallineFrameLifts.residualMap_spec]
  exact RingHom.ext (fun x => ConcreteCategory.congr_hom he x)

theorem lift (Q : C) (i : σ) :
    FrameLifts.BigCrystallineFrameLifts.lift p W B σ J δ base a ((postcompose p W A B J δ base φ).obj Q) i =
      FrameLifts.BigCrystallineFrameLifts.lift p W A σ J δ bA (φ ∘ a) Q i := by
  let l : Q.ring ⧸ Q.ideal → Q.ring := fun x => (Ideal.Quotient.mk_surjective x).choose
  change l (pulledResidual p W A B J δ base φ Q (a i)) =
    l (FrameLifts.BigCrystallineFrameLifts.residualMap p W A J δ bA Q (φ (a i)))
  exact congrArg l (RingHom.congr_fun (residual p W A B J δ base φ Q) (a i))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.PullbackLifts.BigCrystallinePullbackLifts

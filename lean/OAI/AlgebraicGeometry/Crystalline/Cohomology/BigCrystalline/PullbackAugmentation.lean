import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.PullbackResolution
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.RelativeAugmentation

/-! # Pullback Augmentation -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.PullbackAugmentation.BigCrystallinePullbackAugmentation

noncomputable section

/-! # Geometric affine pullback preserves the original frame augmentation -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped TensorProduct

open OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameLifts.BigCrystallineFrameLifts

universe u

variable (p : ℕ) (W A B σ : Type u) [CommRing W] [CommRing A] [CommRing B]
  (J : Ideal W) (δ : DividedPowers J) (base : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of W))
  (φ : B →+* A) (a : σ → B) [Fintype σ]

local notation "bA" => Spec.map (CommRingCat.ofHom φ) ≫ base
local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameLifts.BigCrystallineFrameLifts.Site p W A J δ bA
local notation "ι" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.PullbackLifts.BigCrystallinePullbackLifts.postcompose p W A B J δ base φ
local notation "F" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.PullbackResolution.BigCrystallinePullbackResolution.restriction p W A B J δ base φ
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.modulePresheaf (p := p) (J := J) (δ := δ) base
local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.modulePresheaf (p := p) (J := J) (δ := δ) bA
local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameResolution.BigCrystallineFrameResolution.complex (p := p) (J := J) (δ := δ) (base := base) a
local notation "α" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameResolution.BigCrystallineFrameResolution.augmentation (p := p) (J := J) (δ := δ) (base := base) a
local notation "β" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameResolution.BigCrystallineFrameResolution.augmentation (p := p) (J := J) (δ := δ) (base := bA) (φ ∘ a)

def sourceIso : (F).obj G ≅ H := Iso.refl _

def augmentation : (CochainComplex.single₀ (Cᵒᵖ ⥤ ModuleCat W)).obj ((F).obj G) ⟶
    ((F).mapHomologicalComplex (.up ℕ)).obj K :=
  (HomologicalComplex.singleMapHomologicalComplex F (.up ℕ) 0).inv.app G ≫
    ((F).mapHomologicalComplex (.up ℕ)).map α

theorem zero (Q : Cᵒᵖ) (x : (H).obj Q) :
    (((PullbackResolution.BigCrystallinePullbackResolution.iso p W A B σ J δ base φ a).hom.f 0).app Q).hom
      ((((α).f 0).app ((ι).op.obj Q)).hom x) = (((β).f 0).app Q).hom x := by
  change Q.unop.ring at x
  let t := (((PullbackResolution.BigCrystallinePullbackResolution.iso p W A B σ J δ base φ a).hom.f 0).app Q).hom
  have h₁ := congrArg t (RelativeAugmentation.BigCrystallineRelativeAugmentation.original_zero a ((ι).op.obj Q) x)
  have h₂ := RelativeAugmentation.BigCrystallineRelativeAugmentation.original_zero (φ ∘ a) Q x
  apply h₁.trans
  apply Eq.trans _ h₂.symm
  rfl

theorem square : augmentation p W A B σ J δ base φ a ≫
      (PullbackResolution.BigCrystallinePullbackResolution.iso p W A B σ J δ base φ a).hom =
    (CochainComplex.single₀ _).map (sourceIso p W A B J δ base φ).hom ≫ β := by
  apply HomologicalComplex.from_single_hom_ext
  apply NatTrans.ext
  funext Q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change Q.unop.ring at x
  exact zero p W A B σ J δ base φ a Q x

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.PullbackAugmentation.BigCrystallinePullbackAugmentation

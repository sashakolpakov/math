import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.PullbackResolution
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.RelativeForms

/-! # Pullback Coordinate Forms -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.PullbackCoordinateForms.BigCrystallinePullbackCoordinateForms

noncomputable section

/-! # The original geometric frame identification in relative-form coordinates -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) (W A B σ : Type u) [CommRing W] [CommRing A] [CommRing B]
  (J : Ideal W) (δ : DividedPowers J)
  (base : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of W))
  (φ : B →+* A) (a : σ → B) [Fintype σ]

local notation "bA" => Spec.map (CommRingCat.ofHom φ) ≫ base
local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameLifts.BigCrystallineFrameLifts.Site p W A J δ bA
local notation "ι" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.PullbackLifts.BigCrystallinePullbackLifts.postcompose p W A B J δ base φ
local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameResolution.BigCrystallineFrameResolution.complex (p := p) (J := J) (δ := δ) (base := base) a

theorem component (Q : Cᵒᵖ) (j : ℕ) (z : ((K).X j).obj ((ι).op.obj Q)) :
    ((PullbackResolution.BigCrystallinePullbackResolution.iso p W A B σ J δ base φ a).hom.f j).app Q z = z := by
  change TensorProduct.map LinearMap.id LinearMap.id z = z
  rw [TensorProduct.map_id]
  rfl

variable [LinearOrder σ]

theorem coordinates (Q : Cᵒᵖ) (j : ℕ) (z : ((K).X j).obj ((ι).op.obj Q)) :
    ((RelativeForms.BigCrystallineRelativeForms.complexIso (p := p) (J := J) (δ := δ) (base := bA) (φ ∘ a)).hom.f j).app Q
      (((PullbackResolution.BigCrystallinePullbackResolution.iso p W A B σ J δ base φ a).hom.f j).app Q z) =
    ((RelativeForms.BigCrystallineRelativeForms.complexIso (p := p) (J := J) (δ := δ) (base := base) a).hom.f j).app
      ((ι).op.obj Q) z :=
  congrArg (fun z =>
    ((RelativeForms.BigCrystallineRelativeForms.complexIso (p := p) (J := J) (δ := δ) (base := bA) (φ ∘ a)).hom.f j).app Q z)
      (component p W A B σ J δ base φ a Q j z)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.PullbackCoordinateForms.BigCrystallinePullbackCoordinateForms

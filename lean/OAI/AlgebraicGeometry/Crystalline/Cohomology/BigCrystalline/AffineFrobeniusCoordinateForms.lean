import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.AffineFrobeniusFrames
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameCoordinateSquares
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.PullbackCoordinateForms

/-! # Affine Frobenius Coordinate Forms -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.AffineFrobeniusCoordinateForms.BigCrystallineAffineFrobeniusCoordinateForms

noncomputable section

/-! # Actual geometric Frobenius frame maps in relative-form coordinates -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) (hp : p.Prime) (W A σ : Type u) [CommRing W] [CommRing A]
  (hA : (p : A) = 0) (J : Ideal W) (δ : DividedPowers J)
  (base : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of W))
  (a : σ → A) [Fintype σ] [LinearOrder σ]

local notation "φ" => OAI.AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.powerRingHom p hp A hA
local notation "bF" => Spec.map (CommRingCat.ofHom φ) ≫ base
local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameLifts.BigCrystallineFrameLifts.Site p W A J δ bF
local notation "ι" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.PullbackLifts.BigCrystallinePullbackLifts.postcompose p W A A J δ base φ
local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameResolution.BigCrystallineFrameResolution.complex (p := p) (J := J) (δ := δ) (base := base) a
local notation "c" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.RelativeForms.BigCrystallineRelativeForms.complexIso (p := p) (J := J) (δ := δ) (base := bF) a
local notation "d" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.RelativeForms.BigCrystallineRelativeForms.complexIso (p := p) (J := J) (δ := δ) (base := base) a

theorem coordinates (Q : Cᵒᵖ) (j : ℕ) (z : ((K).X j).obj ((ι).op.obj Q)) :
    ((c).hom.f j).app Q
      (((AffineFrobeniusFrames.BigCrystallineAffineFrobeniusFrames.complexMap p hp W A σ hA J δ base a).f j).app Q z) =
    (PowerForms.BigCrystallinePowerForms.component a p Q).f j (((d).hom.f j).app ((ι).op.obj Q) z) := by
  let z' := ((PullbackResolution.BigCrystallinePullbackResolution.iso p W A A σ J δ base φ a).hom.f j).app Q z
  have hpower := congrArg (fun f => (f.f j).app Q)
    (FrameCoordinateSquares.BigCrystallineFrameCoordinateSquares.power p W A J δ bF a p)
  have hpower' := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hpower) z'
  have hg := PullbackCoordinateForms.BigCrystallinePullbackCoordinateForms.coordinates p W A A σ J δ base φ a Q j z
  exact hpower'.trans (congrArg (fun ω => (PowerForms.BigCrystallinePowerForms.component a p Q).f j ω) hg)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.AffineFrobeniusCoordinateForms.BigCrystallineAffineFrobeniusCoordinateForms

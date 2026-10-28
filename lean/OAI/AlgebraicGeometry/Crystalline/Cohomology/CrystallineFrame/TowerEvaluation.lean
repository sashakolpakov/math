import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.LimitEvaluation
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Adjunction

/-! # Tower Evaluation -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.TowerEvaluation.CrystallineFrameTowerEvaluation

noncomputable section

/-! # Evaluating actual native frame sections on the original polynomial tower -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B]
  (r : MvPolynomial σ (WittVector p k) →+* B) (hr : Function.Surjective r)
  (hbase : r.comp (algebraMap (WittVector p k) (MvPolynomial σ (WittVector p k))) =
    (algebraMap k B).comp WittVector.constantCoeff)

local notation "W" => WittVector p k
local notation "Poly" => MvPolynomial σ W
local notation "a" => fun i => r (MvPolynomial.X i)
local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B
local notation "G" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.Category.FramedCrystallineCategory.frame p k B σ a
local notation "U" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.Category.FramedCrystallineCategory.forget p k B σ a
local notation "P" => Functor.op U ⋙ OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.functions p k X
local notation "Tower" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.EnvelopeFrames.AffineEnvelopeFrames.tower p k B Poly r hr hbase

def evaluation (n : ℕ) :
    DividedPowerAlgebra (FramedPolynomial.Levels.FramedPolynomialLevels.base p k B σ r hr hbase n).thickening.ring
      (σ →₀ (FramedPolynomial.Levels.FramedPolynomialLevels.base p k B σ r hr hbase n).thickening.ring) →ₗ[W]
    (FramedPolynomial.Levels.FramedPolynomialLevels.base p k B σ r hr hbase n).thickening.ring :=
  (Evaluation.CrystallineFrameEvaluation.ambientMap p k B σ a
    (𝟙 (FramedPolynomial.Levels.FramedPolynomialLevels.base p k B σ r hr hbase n))
    (FramedPolynomial.Levels.FramedPolynomialLevels.level p k B σ r hr hbase n).coordinate
    (FramedPolynomial.Levels.FramedPolynomialLevels.level p k B σ r hr hbase n).reduction_coordinate).toLinearMap

theorem coefficient (n : ℕ) (x : PD.InverseLimit.PDInverseLimit.Ring p k B Tower) :
    evaluation p k B σ r hr hbase n
      (((FunctionLimit.CrystallineFrameFunctionLimit.completedCone p k B σ r hr hbase).π.app
        (op (FramedPolynomial.Levels.FramedPolynomialLevels.base p k B σ r hr hbase n))).hom x) =
      PD.InverseLimit.PDInverseLimit.eval p k B Tower n x := by
  rw [LimitEvaluation.CrystallineFrameLimitEvaluation.nativeProjection]
  let Q := FramedPolynomial.Levels.FramedPolynomialLevels.base p k B σ r hr hbase n
  let L := FramedPolynomial.Levels.FramedPolynomialLevels.level p k B σ r hr hbase n
  let f : L ⟶ (G).obj Q := Adjunction.CrystallineFrameAdjunction.homEquiv p k B σ a L Q (𝟙 Q)
  have h : (LimitEvaluation.CrystallineFrameLimitEvaluation.framedCone p k B σ r hr hbase).π.app (op ((G).obj Q)) ≫
      (P).map f.op = ModuleCat.ofHom (PD.InverseLimit.PDInverseLimit.eval p k B Tower n).toLinearMap :=
    ((LimitEvaluation.CrystallineFrameLimitEvaluation.framedCone p k B σ r hr hbase).w f.op).trans
      (LimitEvaluation.CrystallineFrameLimitEvaluation.towerProjection p k B σ r hr hbase n)
  exact ConcreteCategory.congr_hom h x

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.TowerEvaluation.CrystallineFrameTowerEvaluation

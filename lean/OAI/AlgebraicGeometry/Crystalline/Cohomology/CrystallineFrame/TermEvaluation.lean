import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.TowerEvaluation
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.TermLimit

/-! # Term Evaluation -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.TermEvaluation.CrystallineFrameTermEvaluation

noncomputable section

/-! # Actual native term projections recover the original completed tensor coordinates -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open scoped TensorProduct

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B]
  (r : MvPolynomial σ (WittVector p k) →+* B) (hr : Function.Surjective r)
  (hbase : r.comp (algebraMap (WittVector p k) (MvPolynomial σ (WittVector p k))) =
    (algebraMap k B).comp WittVector.constantCoeff)

local notation "W" => WittVector p k
local notation "Poly" => MvPolynomial σ W
local notation "a" => fun i => r (MvPolynomial.X i)
local notation "Tower" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.EnvelopeFrames.AffineEnvelopeFrames.tower p k B Poly r hr hbase
local notation "Completed" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.InverseLimit.PDInverseLimit.Ring p k B Tower

theorem coefficient_map (n : ℕ) :
    (TowerEvaluation.CrystallineFrameTowerEvaluation.evaluation p k B σ r hr hbase n).comp
      ((FunctionLimit.CrystallineFrameFunctionLimit.completedCone p k B σ r hr hbase).π.app
        (op (FramedPolynomial.Levels.FramedPolynomialLevels.base p k B σ r hr hbase n))).hom =
    (PD.InverseLimit.PDInverseLimit.eval p k B Tower n).toLinearMap :=
  LinearMap.ext (TowerEvaluation.CrystallineFrameTowerEvaluation.coefficient p k B σ r hr hbase n)

variable [Fintype σ] [LinearOrder σ]

def evaluation (n j : ℕ) :
    ((Resolution.CrystallineFrameResolution.complex p k B σ a).X j).obj
      (op (FramedPolynomial.Levels.FramedPolynomialLevels.base p k B σ r hr hbase n)) →ₗ[W]
    Koszul.Tensor.KoszulTensor.Term W σ (FramedPolynomial.Levels.FramedPolynomialLevels.base p k B σ r hr hbase n).thickening.ring j :=
  TensorProduct.map (TowerEvaluation.CrystallineFrameTowerEvaluation.evaluation p k B σ r hr hbase n) LinearMap.id

omit [LinearOrder σ] in
theorem projection (n j : ℕ) (x : Koszul.Tensor.KoszulTensor.Term W σ Completed j) :
    evaluation p k B σ r hr hbase n j
      ((TermLimit.CrystallineFrameTermLimit.cone p k B σ r hr hbase j).π.app
      (op (FramedPolynomial.Levels.FramedPolynomialLevels.base p k B σ r hr hbase n)) x) =
    TensorProduct.map (PD.InverseLimit.PDInverseLimit.eval p k B Tower n).toLinearMap LinearMap.id x := by
  let Rn := (FramedPolynomial.Levels.FramedPolynomialLevels.base p k B σ r hr hbase n).thickening.ring
  let f : Completed →ₗ[W] DividedPowerAlgebra Rn (σ →₀ Rn) :=
    ((FunctionLimit.CrystallineFrameFunctionLimit.completedCone p k B σ r hr hbase).π.app
      (op (FramedPolynomial.Levels.FramedPolynomialLevels.base p k B σ r hr hbase n))).hom
  let g : DividedPowerAlgebra Rn (σ →₀ Rn) →ₗ[W] Rn :=
    TowerEvaluation.CrystallineFrameTowerEvaluation.evaluation p k B σ r hr hbase n
  have h : g.comp f = (PD.InverseLimit.PDInverseLimit.eval p k B Tower n).toLinearMap :=
    coefficient_map p k B σ r hr hbase n
  change TensorProduct.map g LinearMap.id (TensorProduct.map f LinearMap.id x) = _
  rw [TensorProduct.map_map, LinearMap.id_comp, h]
  rfl

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.TermEvaluation.CrystallineFrameTermEvaluation

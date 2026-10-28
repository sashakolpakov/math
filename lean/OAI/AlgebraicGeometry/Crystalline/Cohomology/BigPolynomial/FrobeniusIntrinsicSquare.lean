import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigPolynomial.FrobeniusCoordinates
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigPolynomial.IntrinsicFormEvaluation

/-! # Frobenius Intrinsic Square -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigPolynomial.FrobeniusIntrinsicSquare.BigPolynomialFrobeniusIntrinsicSquare

noncomputable section

/-! # Actual native evaluation intertwines the original raw polynomial Frobenius maps -/

universe u

variable (p : ℕ) [Fact p.Prime] (k σ : Type u) [Field k] [CharP k p] [PerfectRing k p]
  [Fintype σ] [LinearOrder σ]

local notation "W" => WittVector p k
local notation "R" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigPolynomial.FrobeniusEvaluation.BigPolynomialFrobeniusEvaluation.ring p k σ
local notation "G" => fun n => DividedPowerAlgebra (R n) (σ →₀ R n)

theorem square (n j : ℕ) (z : Koszul.Tensor.KoszulTensor.Term W σ (G n) j) :
    IntrinsicFormEvaluation.BigPolynomialIntrinsicFormEvaluation.native p k σ n j
      (FrobeniusSectionGenerators.BigPolynomialFrobeniusSectionGenerators.rawMap p k σ j n (ULift.up z)).down =
    WittPolynomial.FrameFrobenius.WittPolynomialFrameFrobenius.formsMap p k σ n j
      (IntrinsicFormEvaluation.BigPolynomialIntrinsicFormEvaluation.native p k σ n j z) := by
  let c := FrobeniusFormSquare.BigPolynomialFrobeniusFormSquare.coordinates p k σ n j
  let E := FrobeniusFormEvaluation.BigPolynomialFrobeniusFormEvaluation.evaluation p k σ n j
  let F := WittPolynomial.FrameFrobenius.WittPolynomialFrameFrobenius.formsMap p k σ n j
  have hn := DFunLike.congr_fun (IntrinsicFormEvaluation.BigPolynomialIntrinsicFormEvaluation.comparison p k σ n j)
    (FrobeniusSectionGenerators.BigPolynomialFrobeniusSectionGenerators.rawMap p k σ j n (ULift.up z)).down
  have hc := congrArg E (FrobeniusCoordinates.BigPolynomialFrobeniusRawCoordinates.coordinates p k σ n j z)
  have hf := DFunLike.congr_fun (FrobeniusFormSquare.BigPolynomialFrobeniusFormSquare.square p k σ n j) (c z)
  have hs := congrArg F (DFunLike.congr_fun (IntrinsicFormEvaluation.BigPolynomialIntrinsicFormEvaluation.comparison p k σ n j) z).symm
  exact hn.trans (hc.trans (hf.trans hs))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigPolynomial.FrobeniusIntrinsicSquare.BigPolynomialFrobeniusIntrinsicSquare

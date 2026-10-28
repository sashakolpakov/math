import OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.SectionEvaluation
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigPolynomial.FrobeniusFormSquare
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicResolution

/-! # Intrinsic Form Evaluation -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigPolynomial.IntrinsicFormEvaluation.BigPolynomialIntrinsicFormEvaluation

noncomputable section

/-! # The actual native evaluation agrees with the polynomial relative-form evaluator -/

open _root_.CategoryTheory Opposite
open scoped TensorProduct

universe u

variable (p : ℕ) [Fact p.Prime] (k σ : Type u) [Field k] [CharP k p]
  [Fintype σ] [LinearOrder σ]

local notation "W" => WittVector p k
local notation "B" => MvPolynomial σ k
local notation "r" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.AbsoluteFrobenius.PolynomialAbsoluteFrobenius.reduction p k σ
local notation "hr" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Residue.WittPolynomialResidue.reduction_surjective p k σ
local notation "hb" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Residue.WittPolynomialResidue.reduction_base p k σ
local notation "a" => fun i => r (MvPolynomial.X i)
local notation "R" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigPolynomial.FrobeniusEvaluation.BigPolynomialFrobeniusEvaluation.ring p k σ
local notation "I" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigPolynomial.FrobeniusEvaluation.BigPolynomialFrobeniusEvaluation.ideal p k σ
local notation "δ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigPolynomial.FrobeniusEvaluation.BigPolynomialFrobeniusEvaluation.dividedPowers p k σ
local notation "G" => fun n => DividedPowerAlgebra (R n) (σ →₀ R n)

def native (n j : ℕ) : Koszul.Tensor.KoszulTensor.Term W σ (G n) j →+
    PD.DeRham.PDDeRham.Form W (R n) (I n) (δ n) j :=
  (Affine.SectionEvaluation.AffineSectionEvaluation.evaluation p k B σ r hr hb j n).toAddMonoidHom.comp
    (((BigCrystalline.IntrinsicResolution.BigCrystallineIntrinsicResolution.iso p k B σ a).hom.f j).app
      (op (FrobeniusMorphism.BigPolynomialFrobeniusMorphism.nativeLevel p k σ n))).hom.toAddMonoidHom

omit [LinearOrder σ] in
theorem native_word (n j : ℕ) (b : G n) (v : Fin j → σ) :
    native p k σ n j (b ⊗ₜ[W] exteriorPower.ιMulti W j (fun l => Finsupp.single (v l) 1)) =
      PD.DeRham.PDDeRham.symbol W (R n) (I n) (δ n) (FrobeniusEvaluation.BigPolynomialFrobeniusEvaluation.evaluation p k σ n b)
        (FrobeniusEvaluation.BigPolynomialFrobeniusEvaluation.liftedCoordinate p k σ n ∘ v) :=
  PD.FormsTensor.PDFormsTensor.toForms_word W (R n) σ (I n) (δ n)
    (FrobeniusEvaluation.BigPolynomialFrobeniusEvaluation.liftedCoordinate p k σ n) j
    (FrobeniusEvaluation.BigPolynomialFrobeniusEvaluation.evaluation p k σ n b) v

theorem comparison (n j : ℕ) :
    native p k σ n j = (FrobeniusFormEvaluation.BigPolynomialFrobeniusFormEvaluation.evaluation p k σ n j).comp
      (FrobeniusFormSquare.BigPolynomialFrobeniusFormSquare.coordinates p k σ n j) := by
  apply TensorExterior.TensorExteriorAdditiveExt.ext W σ (G n) (PD.DeRham.PDDeRham.Form W (R n) (I n) (δ n) j) j
  intro b v
  have hc := FreeRelative.ScalarComparison.FreeRelativeScalarComparison.word W (R n) σ (I n) (δ n) j b v
  have he := (congrArg (FrobeniusFormEvaluation.BigPolynomialFrobeniusFormEvaluation.evaluation p k σ n j) hc).trans
    (FrobeniusFormEvaluation.BigPolynomialFrobeniusFormEvaluation.evaluation_symbol p k σ n j b v)
  exact (native_word p k σ n j b v).trans he.symm

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigPolynomial.IntrinsicFormEvaluation.BigPolynomialIntrinsicFormEvaluation

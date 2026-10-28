import OAI.AlgebraicGeometry.Crystalline.Cohomology.Big.AffineSectionEvaluation
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigPolynomial.FrobeniusIntrinsicSquare

/-! # Polynomial Frobenius Evaluation -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigPolynomial.PolynomialFrobeniusEvaluation.BigPolynomialFrobeniusEvaluation

noncomputable section

/-! # Original completed polynomial section coordinates intertwine geometric crystalline Frobenius -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open _root_.CategoryTheory.Abelian

universe u

variable (p : ℕ) [Fact p.Prime] (k σ : Type u) [Field k] [CharP k p] [PerfectRing k p]
  [Fintype σ] [LinearOrder σ]

local notation "W" => WittVector p k
local notation "B" => MvPolynomial σ k
local notation "r" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.AbsoluteFrobenius.PolynomialAbsoluteFrobenius.reduction p k σ
local notation "hr" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Residue.WittPolynomialResidue.reduction_surjective p k σ
local notation "hb" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Residue.WittPolynomialResidue.reduction_base p k σ
local notation "a" => fun i => r (MvPolynomial.X i)
local notation "I" => Ideal.span {(p : W)}
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B
local notation "bX" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k X
local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameSheafResolution.BigCrystallineFrameSheafResolution.complex p W B I γ bX a
local notation "A₀" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.constantUnit (p := p) (J := I) (δ := γ) bX
local notation "Tower" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.EnvelopeFrames.AffineEnvelopeFrames.tower p k B (MvPolynomial σ W) r hr hb
local notation "e" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Big.AffineComparison.BigAffineCrystallineComparison.complexIso p k B σ r hr hb

def evaluationMap (j n : ℕ) (α : (BigCrystalline.FrameSectionComparison.BigCrystallineFrameSectionComparison.complex p k B σ r).X j) :=
  PD.PDDeRham.eval p k B Tower j n (((e).hom.f j α).down.down)

def evaluation (j n : ℕ) (x : A₀ ⟶ (K).X j) :=
  evaluationMap p k σ j n (Ext.mk₀ x)

theorem section_evaluation (j n : ℕ) (x : A₀ ⟶ (K).X j) :
    evaluation p k σ j n (BigCrystalline.FrobeniusSectionHom.BigCrystallineFrobeniusSectionHom.frobenius p k B σ r j x) =
      WittPolynomial.FrameFrobenius.WittPolynomialFrameFrobenius.formsMap p k σ n j (evaluation p k σ j n x) := by
  let x' := BigCrystalline.FrobeniusSectionHom.BigCrystallineFrobeniusSectionHom.frobenius p k B σ r j x
  let z := BigCrystalline.IntrinsicGeneratorSections.BigCrystallineIntrinsicGeneratorSections.representative p k B σ a j x
    (FrobeniusMorphism.BigPolynomialFrobeniusMorphism.nativeLevel p k σ n)
  have hF := Big.AffineSectionEvaluation.BigAffineSectionEvaluation.component p k B σ r hr hb j n x'
  have hrep := congrArg (fun z => IntrinsicFormEvaluation.BigPolynomialIntrinsicFormEvaluation.native p k σ n j z.down)
    (FrobeniusSectionGenerators.BigPolynomialFrobeniusSectionGenerators.representative p k σ j n x)
  have hs := FrobeniusIntrinsicSquare.BigPolynomialFrobeniusIntrinsicSquare.square p k σ n j z.down
  have h₀ := congrArg (WittPolynomial.FrameFrobenius.WittPolynomialFrameFrobenius.formsMap p k σ n j)
    (Big.AffineSectionEvaluation.BigAffineSectionEvaluation.component p k B σ r hr hb j n x).symm
  exact hF.trans (hrep.trans (hs.trans h₀))

theorem original_mk (j n : ℕ) (x : A₀ ⟶ (K).X j) :
    evaluationMap p k σ j n
      ((BigCrystalline.AffineFrobeniusNaturality.BigCrystallineAffineFrobeniusNaturality.complexMap p k B σ r).f j (Ext.mk₀ x)) =
    WittPolynomial.FrameFrobenius.WittPolynomialFrameFrobenius.formsMap p k σ n j (evaluationMap p k σ j n (Ext.mk₀ x)) :=
  (congrArg (evaluationMap p k σ j n)
    (BigCrystalline.FrobeniusSectionHom.BigCrystallineFrobeniusSectionHom.original_mk p k B σ r j x)).trans
      (section_evaluation p k σ j n x)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigPolynomial.PolynomialFrobeniusEvaluation.BigPolynomialFrobeniusEvaluation

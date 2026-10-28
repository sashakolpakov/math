import OAI.AlgebraicGeometry.Crystalline.Cohomology.Big.AffineComparison
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicGeneratorSections
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.SectionEvaluation

/-! # Affine Section Evaluation -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Big.AffineSectionEvaluation.BigAffineSectionEvaluation

noncomputable section

/-! # Evaluating the original big-site completed comparison on its actual section generators -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open _root_.CategoryTheory.Abelian

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B] [Fintype σ] [LinearOrder σ]
  (r : MvPolynomial σ (WittVector p k) →+* B) (hr : Function.Surjective r)
  (hbase : r.comp (algebraMap (WittVector p k) (MvPolynomial σ (WittVector p k))) =
    (algebraMap k B).comp WittVector.constantCoeff)

local notation "W" => WittVector p k
local notation "R" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.CoefficientRing p k
local notation "Poly" => MvPolynomial σ W
local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B
local notation "I" => Ideal.span {(p : W)}
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "bX" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k X
local notation "a" => fun i => r (MvPolynomial.X i)
local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameSheafResolution.BigCrystallineFrameSheafResolution.complex p W B I γ bX a
local notation "L" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.SheafResolution.CrystallineFrameSheafResolution.complex p k B σ a
local notation "A₀" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.constantUnit (p := p) (J := I) (δ := γ) bX
local notation "T" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.topology p k X
local notation "Tower" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.EnvelopeFrames.AffineEnvelopeFrames.tower p k B Poly r hr hbase

omit [LinearOrder σ] in
theorem ordinary_mk (j : ℕ) (x : A₀ ⟶ (K).X j) :
    (CrystallineFrame.SectionComparison.CrystallineFrameSectionComparison.ordinaryComplexIso p k B σ r).hom.f j
      ((BigCrystalline.IntrinsicSections.BigCrystallineIntrinsicSections.iso p k B σ a).hom.f j (Ext.mk₀ x)) =
    ULift.up (BigCrystalline.IntrinsicSectionCoordinates.BigCrystallineIntrinsicSectionCoordinates.targetSections p k B σ a j
      (BigCrystalline.IntrinsicSectionCoordinates.BigCrystallineIntrinsicSectionCoordinates.transport p k B σ a j x)) :=
  (congrArg (fun z => (CrystallineFrame.SectionComparison.CrystallineFrameSectionComparison.ordinaryComplexIso p k B σ r).hom.f j z)
    (BigCrystalline.IntrinsicSectionCoordinates.BigCrystallineIntrinsicSectionCoordinates.map_mk p k B σ a j x)).trans
      (NumberTheory.PadicHodge.IntegralComparison.Ext.ZeroPresheafSections.equivalence_mk R T ((L).X j)
        (BigCrystalline.IntrinsicSectionCoordinates.BigCrystallineIntrinsicSectionCoordinates.transport p k B σ a j x))

theorem component (j n : ℕ) (x : A₀ ⟶ (K).X j) :
    PD.PDDeRham.eval p k B Tower j n
      (((AffineComparison.BigAffineCrystallineComparison.complexIso p k B σ r hr hbase).hom.f j
        (Ext.mk₀ x)).down.down) =
    Affine.SectionEvaluation.AffineSectionEvaluation.evaluation p k B σ r hr hbase j n
      (((BigCrystalline.IntrinsicGeneratorCoordinates.BigCrystallineIntrinsicGeneratorCoordinates.rawMap p k B σ a j).app
        (op (FramedPolynomial.Levels.FramedPolynomialLevels.base p k B σ r hr hbase n))
          (BigCrystalline.IntrinsicGeneratorSections.BigCrystallineIntrinsicGeneratorSections.representative p k B σ a j x
            (FramedPolynomial.Levels.FramedPolynomialLevels.base p k B σ r hr hbase n))).down) := by
  let s := BigCrystalline.IntrinsicSectionCoordinates.BigCrystallineIntrinsicSectionCoordinates.targetSections p k B σ a j
    (BigCrystalline.IntrinsicSectionCoordinates.BigCrystallineIntrinsicSectionCoordinates.transport p k B σ a j x)
  have ho := congrArg (fun z => PD.PDDeRham.eval p k B Tower j n
    (((Affine.Comparison.AffineCrystallineComparison.complexIso p k B σ r hr hbase).hom.f j z).down.down))
      (ordinary_mk p k B σ r j x)
  have hc := Affine.SectionEvaluation.AffineSectionEvaluation.component p k B σ r hr hbase j n s
  have hg := congrArg ULift.down (BigCrystalline.IntrinsicGeneratorSections.BigCrystallineIntrinsicGeneratorSections.coordinates p k B σ a j x
    (FramedPolynomial.Levels.FramedPolynomialLevels.base p k B σ r hr hbase n))
  exact ho.trans (hc.trans (congrArg (Affine.SectionEvaluation.AffineSectionEvaluation.evaluation p k B σ r hr hbase j n) hg))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Big.AffineSectionEvaluation.BigAffineSectionEvaluation

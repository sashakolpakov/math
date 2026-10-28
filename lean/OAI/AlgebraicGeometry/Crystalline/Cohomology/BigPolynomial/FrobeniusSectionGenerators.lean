import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrobeniusSectionHom
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.TwistGeneratorCoordinates
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicGeneratorSections
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigPolynomial.FrobeniusMorphism
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrobeniusTransport
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrobeniusSectionGenerators

/-! # Frobenius Section Generators -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigPolynomial.FrobeniusSectionGenerators.BigPolynomialFrobeniusSectionGenerators

noncomputable section

/-! # Original polynomial Frobenius acts through the actual raw frame maps on section generators -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable (p : ℕ) [Fact p.Prime] (k σ : Type u) [Field k] [CharP k p] [PerfectRing k p]
  [Fintype σ] [LinearOrder σ]

local notation "W" => WittVector p k
local notation "R" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.CoefficientRing p k
local notation "B" => MvPolynomial σ k
local notation "r" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.AbsoluteFrobenius.PolynomialAbsoluteFrobenius.reduction p k σ
local notation "a" => fun i => r (MvPolynomial.X i)
local notation "I" => Ideal.span {(p : W)}
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B
local notation "bX" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k X
local notation "φ" => OAI.AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.powerRingHom p (Fact.out : p.Prime) B
  (BigCrystalline.AffineFrobeniusComparison.BigCrystallineAffineFrobeniusComparison.prime_zero p k B)
local notation "g" => Spec.map (CommRingCat.ofHom φ)
local notation "bF" => g ≫ bX
local notation "e" => WittVector.frobeniusEquiv p k
local notation "he" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittFrobeniusDP p k
local notation "he'" => OAI.NumberTheory.PadicHodge.PeriodInvariants.WittFrobeniusGeometry.inverse_isDPMorphism p k
local notation "hb" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.AffineFrobeniusComparison.BigCrystallineAffineFrobeniusComparison.over_base p k B
local notation "tw" => OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineBaseTwist.twist (p := p) e (DividedPowers.DPMorphism.isDPMorphism he) hb
local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameSheafResolution.BigCrystallineFrameSheafResolution.complex p W B I γ bX a
local notation "L" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameSheafResolution.BigCrystallineFrameSheafResolution.complex p W B I γ bF a
local notation "A₀" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.constantUnit (p := p) (J := I) (δ := γ) bX
local notation "c" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.AffineFrobeniusSheaves.BigCrystallineAffineFrobeniusSheaves.complexMap p (Fact.out : p.Prime) W B σ
  (BigCrystalline.AffineFrobeniusComparison.BigCrystallineAffineFrobeniusComparison.prime_zero p k B) I γ bX a
local notation "t" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.TwistSheafTransport.BigCrystallineTwistSheafTransport.complexIso p W B I γ bX bF e
  (DividedPowers.DPMorphism.isDPMorphism he) he' hb a

def rawMap (j n : ℕ)
    (z : (BigCrystalline.IntrinsicGenerators.BigCrystallineIntrinsicGenerators.presheaf p k B σ a j).obj
      (op (FrobeniusMorphism.BigPolynomialFrobeniusMorphism.level p k σ n))) :
    (BigCrystalline.IntrinsicGenerators.BigCrystallineIntrinsicGenerators.presheaf p k B σ a j).obj
      (op (FrobeniusMorphism.BigPolynomialFrobeniusMorphism.level p k σ n)) :=
  BigCrystalline.FrobeniusTransport.BigCrystallineFrobeniusRawTransport.map p (Fact.out : p.Prime) W B σ
    (BigCrystalline.AffineFrobeniusComparison.BigCrystallineAffineFrobeniusComparison.prime_zero p k B) I γ bX e (he).isDPMorphism hb a j
    (FrobeniusMorphism.BigPolynomialFrobeniusMorphism.level p k σ n) (FrobeniusMorphism.BigPolynomialFrobeniusMorphism.morphism p k σ n) z

theorem section_generator (j n : ℕ) (x : A₀ ⟶ (K).X j) :
    (BigCrystalline.IntrinsicSectionCoordinates.BigCrystallineIntrinsicSectionCoordinates.sourceSections p k B σ a j
      (BigCrystalline.FrobeniusSectionHom.BigCrystallineFrobeniusSectionHom.frobenius p k B σ r j x)).app
        (op (FrobeniusMorphism.BigPolynomialFrobeniusMorphism.level p k σ n)) (1 : R) =
    (BigCrystalline.IntrinsicGenerators.BigCrystallineIntrinsicGenerators.generator p k B σ a j).app
      (op (FrobeniusMorphism.BigPolynomialFrobeniusMorphism.level p k σ n))
        (rawMap p k σ j n (BigCrystalline.IntrinsicGeneratorSections.BigCrystallineIntrinsicGeneratorSections.representative p k B σ a j x
          (FrobeniusMorphism.BigPolynomialFrobeniusMorphism.nativeLevel p k σ n))) := by
  let z := BigCrystalline.IntrinsicGeneratorSections.BigCrystallineIntrinsicGeneratorSections.representative p k B σ a j x
    (FrobeniusMorphism.BigPolynomialFrobeniusMorphism.nativeLevel p k σ n)
  have hz := BigCrystalline.IntrinsicGeneratorSections.BigCrystallineIntrinsicGeneratorSections.generator_representative p k B σ a j x
    (FrobeniusMorphism.BigPolynomialFrobeniusMorphism.nativeLevel p k σ n)
  have hg := BigCrystalline.FrobeniusSectionGenerators.BigCrystallineFrobeniusSectionGenerators.section_generator p (Fact.out : p.Prime) W B σ
    (BigCrystalline.AffineFrobeniusComparison.BigCrystallineAffineFrobeniusComparison.prime_zero p k B) I γ bX e (he).isDPMorphism he' hb a j x
    (FrobeniusMorphism.BigPolynomialFrobeniusMorphism.level p k σ n) (FrobeniusMorphism.BigPolynomialFrobeniusMorphism.morphism p k σ n) z
    (by
      convert hz using 1 <;>
        simp only [BigCrystalline.FrobeniusSectionGenerators.BigCrystallineFrobeniusSectionGenerators.generator,
          BigCrystalline.IntrinsicGenerators.BigCrystallineIntrinsicGenerators.generator, BigCrystalline.IntrinsicGenerators.BigCrystallineIntrinsicGenerators.presheaf,
          BigCrystalline.FrobeniusTransport.BigCrystallineFrobeniusRawTransport.presheaf,
          BigCrystalline.AffineFrobeniusSectionCoordinates.BigCrystallineAffineFrobeniusSectionCoordinates.sourcePresheaf,
          BigCrystalline.FrobeniusSectionGenerators.BigCrystallineFrobeniusSectionGenerators.sections,
          BigCrystalline.IntrinsicSectionCoordinates.BigCrystallineIntrinsicSectionCoordinates.sourceSections,
          FrobeniusMorphism.BigPolynomialFrobeniusMorphism.level, z] <;> rfl)
  convert hg using 1
  all_goals
    simp only [BigCrystalline.FrobeniusSectionHom.BigCrystallineFrobeniusSectionHom.frobenius,
      BigCrystalline.FrobeniusSectionGenerators.BigCrystallineFrobeniusSectionGenerators.sections, BigCrystalline.IntrinsicSectionCoordinates.BigCrystallineIntrinsicSectionCoordinates.sourceSections,
      BigCrystalline.FrobeniusSectionGenerators.BigCrystallineFrobeniusSectionGenerators.generator,
      BigCrystalline.IntrinsicGenerators.BigCrystallineIntrinsicGenerators.generator, BigCrystalline.IntrinsicGenerators.BigCrystallineIntrinsicGenerators.presheaf,
      BigCrystalline.FrobeniusTransport.BigCrystallineFrobeniusRawTransport.presheaf,
      BigCrystalline.AffineFrobeniusSectionCoordinates.BigCrystallineAffineFrobeniusSectionCoordinates.sourcePresheaf, rawMap, z]
  all_goals rfl

theorem representative (j n : ℕ) (x : A₀ ⟶ (K).X j) :
    BigCrystalline.IntrinsicGeneratorSections.BigCrystallineIntrinsicGeneratorSections.representative p k B σ a j
      (BigCrystalline.FrobeniusSectionHom.BigCrystallineFrobeniusSectionHom.frobenius p k B σ r j x)
      (FrobeniusMorphism.BigPolynomialFrobeniusMorphism.nativeLevel p k σ n) =
    rawMap p k σ j n (BigCrystalline.IntrinsicGeneratorSections.BigCrystallineIntrinsicGeneratorSections.representative p k B σ a j x
      (FrobeniusMorphism.BigPolynomialFrobeniusMorphism.nativeLevel p k σ n)) := by
  let x' : A₀ ⟶ (K).X j := BigCrystalline.FrobeniusSectionHom.BigCrystallineFrobeniusSectionHom.frobenius p k B σ r j x
  let Q := FrobeniusMorphism.BigPolynomialFrobeniusMorphism.nativeLevel p k σ n
  let z := rawMap p k σ j n (BigCrystalline.IntrinsicGeneratorSections.BigCrystallineIntrinsicGeneratorSections.representative p k B σ a j x Q)
  have hs := (section_generator p k σ j n x).symm
  dsimp only [FrobeniusMorphism.BigPolynomialFrobeniusMorphism.level] at hs
  exact BigCrystalline.IntrinsicGeneratorSections.BigCrystallineIntrinsicGeneratorSections.representative_eq p k B σ a j x' Q z (by
    convert hs using 1)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigPolynomial.FrobeniusSectionGenerators.BigPolynomialFrobeniusSectionGenerators

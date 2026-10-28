import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.TwistAcyclic
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.TwistSheafAugmentation
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameSectionComparison
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Semilinear.TransportNaturality

/-! # Twist Comparison -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.TwistComparison.BigCrystallineTwistComparison

noncomputable section

/-! # The original crystalline base-twist Ext map on the actual affine frame complex -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open _root_.CategoryTheory.Abelian

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B] [Fintype σ] [LinearOrder σ]
  (r : MvPolynomial σ (WittVector p k) →+* B) (hr : Function.Surjective r)
  (hbase : r.comp (algebraMap (WittVector p k) (MvPolynomial σ (WittVector p k))) =
    (algebraMap k B).comp WittVector.constantCoeff)

local notation "W" => WittVector p k
local notation "R" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.CoefficientRing p k
local notation "I" => Ideal.span {(p : W)}
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "bX" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k (OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B)
local notation "a" => fun i => r (MvPolynomial.X i)
local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameSheafResolution.BigCrystallineFrameSheafResolution.complex p W B I γ bX a
local notation "A₀" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.constantUnit (p := p) (J := I) (δ := γ) bX

variable (b' : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of (WittVector p k)))
  (e : WittVector p k ≃+* WittVector p k)
  (he : DividedPowers.IsDPMorphism (Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) e.toRingHom)
  (he' : DividedPowers.IsDPMorphism (Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) e.symm.toRingHom)
  (h : b' = NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k
    (AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B) ≫ Spec.map (CommRingCat.ofHom e.toRingHom))

local notation "F" => OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistCohomology.twistedRestriction (p := p) e he he' h
local notation "A₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.constantUnit (p := p) (J := I) (δ := γ) b'
local notation "L" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameSheafResolution.BigCrystallineFrameSheafResolution.complex p W B I γ b' a
local notation "α" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameSheafResolution.BigCrystallineFrameSheafResolution.augmentation p W B I γ b' a
local notation "β" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameSheafResolution.BigCrystallineFrameSheafResolution.augmentation p W B I γ bX a
local notation "τ" => OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistCohomology.coefficientEquiv e

def sourceComplex : CochainComplex (ModuleCat.{u + 2} R) ℕ :=
  NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution.Comparison.complex R A₁ L

def sourceHomologyIso (n : ℕ) : (sourceComplex p k B σ r b').homology n ≅
    ModuleCat.of R (NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.Cohomology (p := p) (J := I) (δ := γ) b' n) :=
  Acyclic.AllDegreesComparison.AcyclicAllDegreesComparison.homologyIso R A₁ L α
    (TwistAcyclic.BigCrystallineTwistAcyclic.source_term p k B σ r hr hbase b' e he he' h) n

def sectionMap : sourceComplex p k B σ r b' ⟶
    ((Semilinear.AcyclicHomologyData.SemilinearAcyclicHomologyData.coefficients R R (τ).toRingHom).mapHomologicalComplex (.up ℕ)).obj
      (FrameSectionComparison.BigCrystallineFrameSectionComparison.complex p k B σ r) :=
  Semilinear.TransportNaturality.SemilinearTransportNaturality.sectionMap R R (τ).toRingHom F
    (NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistCohomology.twistedRestriction_map_smul e he he' h) A₁
    (NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistCohomology.constantTransport (p := p) e he he' h).inv
    (TwistSheafTransport.BigCrystallineTwistSheafTransport.complexIso p W B I γ bX b' e he he' h a).hom

def targetHomologyIso (n : ℕ) :
    (FrameSectionComparison.BigCrystallineFrameSectionComparison.complex p k B σ r).homology n ≅
      ModuleCat.of R (NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.Cohomology (p := p) (J := I) (δ := γ) bX n) :=
  Acyclic.AllDegreesComparison.AcyclicAllDegreesComparison.homologyIso R A₀ K β
    (TwistAcyclic.BigCrystallineTwistAcyclic.target_term p k B σ r hr hbase) n

omit [LinearOrder σ] in
theorem targetHomologyIso_original (n : ℕ) : targetHomologyIso p k B σ r hr hbase n =
    FrameSectionComparison.BigCrystallineFrameSectionComparison.homologyIso p k B σ r hr hbase n := by
  cases n <;> rfl

include hr hbase in
theorem generic_naturality (n : ℕ) (x : (sourceComplex p k B σ r b').homology n) :
    (targetHomologyIso p k B σ r hr hbase n).hom
      ((Mapped.ComplexHomology.MappedComplexHomology.iso (Semilinear.AcyclicHomologyData.SemilinearAcyclicHomologyData.coefficients R R (τ).toRingHom)
          (FrameSectionComparison.BigCrystallineFrameSectionComparison.complex p k B σ r) n).hom
        (HomologicalComplex.homologyMap (sectionMap p k B σ r b' e he he' h) n x)) =
    (Ext.mk₀ (NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistCohomology.constantTransport (p := p) e he he' h).inv).precomp
      (NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.structureSheaf (p := p) (J := I) (δ := γ) bX) (zero_add n)
      ((Ext.mk₀ (NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistCohomology.structureTransport (p := p) e he he' h).hom).postcomp
        ((F).obj A₁) (add_zero n)
        (((sourceHomologyIso p k B σ r hr hbase b' e he he' h n).hom x).mapExactFunctor F)) := by
  exact Semilinear.TransportNaturality.SemilinearTransportNaturality.naturality R R (τ).toRingHom F
    (NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistCohomology.twistedRestriction_map_smul e he he' h) A₁
    (NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistCohomology.constantTransport (p := p) e he he' h).inv
    (TwistSheafTransport.BigCrystallineTwistSheafTransport.complexIso p W B I γ bX b' e he he' h a).hom α β
    (NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistCohomology.structureTransport (p := p) e he he' h).hom
    (TwistSheafAugmentation.BigCrystallineTwistSheafAugmentation.original_square p W B σ I γ bX b' e he he' h a)
    (TwistAcyclic.BigCrystallineTwistAcyclic.source_term p k B σ r hr hbase b' e he he' h)
    (TwistAcyclic.BigCrystallineTwistAcyclic.transported_source_term p k B σ r hr hbase b' e he he' h)
    (TwistAcyclic.BigCrystallineTwistAcyclic.target_term p k B σ r hr hbase) n x

include hr hbase in
theorem naturality (n : ℕ) (x : (sourceComplex p k B σ r b').homology n) :
    (FrameSectionComparison.BigCrystallineFrameSectionComparison.homologyIso p k B σ r hr hbase n).hom
      ((Mapped.ComplexHomology.MappedComplexHomology.iso (Semilinear.AcyclicHomologyData.SemilinearAcyclicHomologyData.coefficients R R (τ).toRingHom)
          (FrameSectionComparison.BigCrystallineFrameSectionComparison.complex p k B σ r) n).hom
        (HomologicalComplex.homologyMap (sectionMap p k B σ r b' e he he' h) n x)) =
    NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistCohomology.cohomologyMap (p := p) e he he' h n
      ((sourceHomologyIso p k B σ r hr hbase b' e he he' h n).hom x) := by
  rw [← targetHomologyIso_original]
  exact (generic_naturality p k B σ r hr hbase b' e he he' h n x).trans
    (TwistEquivalence.CrystallineTwistEquivalence.cohomologyMap_apply e he he' h n
      ((sourceHomologyIso p k B σ r hr hbase b' e he he' h n).hom x)).symm

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.TwistComparison.BigCrystallineTwistComparison

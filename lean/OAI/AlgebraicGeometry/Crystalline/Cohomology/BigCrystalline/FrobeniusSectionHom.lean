import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.AffineFrobeniusNaturality
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.AffineFrobeniusSectionCoordinates
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.TwistSectionCoordinates
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrobeniusSectionComposition

/-! # Frobenius Section Hom -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrobeniusSectionHom.BigCrystallineFrobeniusSectionHom

noncomputable section

/-! # The original crystalline Frobenius on actual degree-zero section representatives -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open _root_.CategoryTheory.Abelian

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p] [PerfectRing k p]
  [CommRing B] [Algebra k B] [Fintype σ] [LinearOrder σ]
  (r : MvPolynomial σ (WittVector p k) →+* B)

local notation "W" => WittVector p k
local notation "R" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.CoefficientRing p k
local notation "I" => Ideal.span {(p : W)}
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B
local notation "bX" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k X
local notation "φ" => OAI.AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.powerRingHom p (Fact.out : p.Prime) B
  (AffineFrobeniusComparison.BigCrystallineAffineFrobeniusComparison.prime_zero p k B)
local notation "g" => Spec.map (CommRingCat.ofHom φ)
local notation "bF" => g ≫ bX
local notation "e" => WittVector.frobeniusEquiv p k
local notation "he" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittFrobeniusDP p k
local notation "he'" => OAI.NumberTheory.PadicHodge.PeriodInvariants.WittFrobeniusGeometry.inverse_isDPMorphism p k
local notation "hb" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.AffineFrobeniusComparison.BigCrystallineAffineFrobeniusComparison.over_base p k B
local notation "a" => fun i => r (MvPolynomial.X i)
local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameSheafResolution.BigCrystallineFrameSheafResolution.complex p W B I γ bX a
local notation "L" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameSheafResolution.BigCrystallineFrameSheafResolution.complex p W B I γ bF a
local notation "A₀" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.constantUnit (p := p) (J := I) (δ := γ) bX
local notation "A₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.constantUnit (p := p) (J := I) (δ := γ) bF
local notation "tw" => OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineBaseTwist.twist (p := p) e (DividedPowers.DPMorphism.isDPMorphism he) hb
local notation "geo" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.PullbackLifts.BigCrystallinePullbackLifts.postcompose p W B B I γ bX φ
local notation "c" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.AffineFrobeniusSheaves.BigCrystallineAffineFrobeniusSheaves.complexMap p (Fact.out : p.Prime) W B σ
  (AffineFrobeniusComparison.BigCrystallineAffineFrobeniusComparison.prime_zero p k B) I γ bX a
local notation "t" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.TwistSheafTransport.BigCrystallineTwistSheafTransport.complexIso p W B I γ bX bF e
  (DividedPowers.DPMorphism.isDPMorphism he) he' hb a
local notation "U" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite.Object.topology (p := p) (J := I) (δ := γ) (f := bX)

def geometric (j : ℕ) (x : A₀ ⟶ (K).X j) : A₁ ⟶ (L).X j :=
  AffineFrobeniusSectionCoordinates.BigCrystallineAffineFrobeniusSectionCoordinates.transport p (Fact.out : p.Prime) W B σ
    (AffineFrobeniusComparison.BigCrystallineAffineFrobeniusComparison.prime_zero p k B) I γ bX a j x

def frobenius (j : ℕ) (x : A₀ ⟶ (K).X j) : A₀ ⟶ (K).X j :=
  FrobeniusSectionComposition.BigCrystallineFrobeniusSectionComposition.transport p (Fact.out : p.Prime) W B σ
    (AffineFrobeniusComparison.BigCrystallineAffineFrobeniusComparison.prime_zero p k B) I γ bX e (he).isDPMorphism he' hb a j x

omit [PerfectRing k p] in
theorem geometric_mk (j : ℕ) (x : A₀ ⟶ (K).X j) :
    (AffineFrobeniusComparison.BigCrystallineAffineFrobeniusComparison.sectionMap p k B σ r).f j (Ext.mk₀ x) =
      Ext.mk₀ (geometric p k B σ r j x) :=
  AffineFrobeniusSectionCoordinates.BigCrystallineAffineFrobeniusSectionCoordinates.ext_map_mk p (Fact.out : p.Prime) W B σ
    (AffineFrobeniusComparison.BigCrystallineAffineFrobeniusComparison.prime_zero p k B) I γ bX a j x

theorem twist_mk (j : ℕ) (x : A₁ ⟶ (L).X j) :
    (TwistComparison.BigCrystallineTwistComparison.sectionMap p k B σ r bF e (he).isDPMorphism he' hb).f j (Ext.mk₀ x) =
      Ext.mk₀ (TwistSectionCoordinates.BigCrystallineTwistSectionCoordinates.transport p W B I γ bX bF e
        (he).isDPMorphism he' hb a j x) :=
  TwistSectionCoordinates.BigCrystallineTwistSectionCoordinates.ext_map_mk p W B I γ bX bF e (he).isDPMorphism he' hb a j x

theorem original_mk (j : ℕ) (x : A₀ ⟶ (K).X j) :
    (AffineFrobeniusNaturality.BigCrystallineAffineFrobeniusNaturality.complexMap p k B σ r).f j (Ext.mk₀ x) =
      Ext.mk₀ (frobenius p k B σ r j x) :=
  (congrArg (fun z => (TwistComparison.BigCrystallineTwistComparison.sectionMap p k B σ r bF e
    (he).isDPMorphism he' hb).f j z) (geometric_mk p k B σ r j x)).trans
      (twist_mk p k B σ r j (geometric p k B σ r j x))

theorem sections_apply (j : ℕ) (x : A₀ ⟶ (K).X j)
    (V : (FrameLifts.BigCrystallineFrameLifts.Site p W B I γ bX)ᵒᵖ) :
    (NumberTheory.PadicHodge.IntegralComparison.Ext.ZeroPresheafSections.homLinearEquiv R U ((K).X j)
      (frobenius p k B σ r j x)).app V (1 : R) =
    ((t).hom.f j).hom.app V
      (((c).f j).hom.app ((tw).op.obj V)
        ((NumberTheory.PadicHodge.IntegralComparison.Ext.ZeroPresheafSections.homLinearEquiv R U ((K).X j) x).app
          ((geo).op.obj ((tw).op.obj V)) (1 : R))) := by
  convert FrobeniusSectionComposition.BigCrystallineFrobeniusSectionComposition.sections_apply p (Fact.out : p.Prime) W B σ
    (AffineFrobeniusComparison.BigCrystallineAffineFrobeniusComparison.prime_zero p k B) I γ bX e (he).isDPMorphism he' hb a j x V using 1
  simp only [frobenius]

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrobeniusSectionHom.BigCrystallineFrobeniusSectionHom

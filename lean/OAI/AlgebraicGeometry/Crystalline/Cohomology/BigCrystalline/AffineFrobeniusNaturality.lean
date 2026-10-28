import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.AffineFrobeniusComparison
import OAI.AlgebraicGeometry.Crystalline.Cohomology.FrobeniusFactorization

/-! # Affine Frobenius Naturality -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.AffineFrobeniusNaturality.BigCrystallineAffineFrobeniusNaturality

noncomputable section

/-! # The original crystalline Frobenius on the affine frame section complex -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p] [PerfectRing k p]
  [CommRing B] [Algebra k B] [Fintype σ] [LinearOrder σ]
  (r : MvPolynomial σ (WittVector p k) →+* B) (hr : Function.Surjective r)
  (hbase : r.comp (algebraMap (WittVector p k) (MvPolynomial σ (WittVector p k))) =
    (algebraMap k B).comp WittVector.constantCoeff)

local notation "W" => WittVector p k
local notation "R" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.CoefficientRing p k
local notation "I" => Ideal.span {(p : W)}
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "X₀" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B
local notation "bX" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k X₀
local notation "φ" => OAI.AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.powerRingHom p (Fact.out : p.Prime) B
  (AffineFrobeniusComparison.BigCrystallineAffineFrobeniusComparison.prime_zero p k B)
local notation "g" => Spec.map (CommRingCat.ofHom φ)
local notation "bF" => g ≫ bX
local notation "e" => WittVector.frobeniusEquiv p k
local notation "he" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittFrobeniusDP p k
local notation "he'" => OAI.NumberTheory.PadicHodge.PeriodInvariants.WittFrobeniusGeometry.inverse_isDPMorphism p k
local notation "hb" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.AffineFrobeniusComparison.BigCrystallineAffineFrobeniusComparison.over_base p k B
local notation "τ" => OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistCohomology.coefficientEquiv e
local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameSectionComparison.BigCrystallineFrameSectionComparison.complex p k B σ r
abbrev coefficients : ModuleCat.{u + 2} R ⥤ ModuleCat.{u + 2} R :=
  Semilinear.AcyclicHomologyData.SemilinearAcyclicHomologyData.coefficients R R (τ).toRingHom

local notation "Q" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.AffineFrobeniusNaturality.BigCrystallineAffineFrobeniusNaturality.coefficients p k

def complexMap : K ⟶ ((Q).mapHomologicalComplex (.up ℕ)).obj K :=
  AffineFrobeniusComparison.BigCrystallineAffineFrobeniusComparison.sectionMap p k B σ r ≫
    TwistComparison.BigCrystallineTwistComparison.sectionMap p k B σ r bF e (he).isDPMorphism he' hb

include hr hbase in
theorem original (n : ℕ) (x : (K).homology n) :
    (FrameSectionComparison.BigCrystallineFrameSectionComparison.homologyIso p k B σ r hr hbase n).hom
      ((Mapped.ComplexHomology.MappedComplexHomology.iso Q K n).hom
        (HomologicalComplex.homologyMap (complexMap p k B σ r) n x)) =
    NumberTheory.PadicHodge.PeriodInvariants.CrystallineFrobenius.bigFrobenius p k X₀ n
      ((FrameSectionComparison.BigCrystallineFrameSectionComparison.homologyIso p k B σ r hr hbase n).hom x) := by
  let f := AffineFrobeniusComparison.BigCrystallineAffineFrobeniusComparison.sectionMap p k B σ r
  let t := TwistComparison.BigCrystallineTwistComparison.sectionMap p k B σ r bF e (he).isDPMorphism he' hb
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u + 2} R) (.up ℕ) n
  let v := (FrameSectionComparison.BigCrystallineFrameSectionComparison.homologyIso p k B σ r hr hbase n).hom
  let m := (Mapped.ComplexHomology.MappedComplexHomology.iso Q K n).hom
  have hc : HomologicalComplex.homologyMap (complexMap p k B σ r) n x =
      HomologicalComplex.homologyMap t n (HomologicalComplex.homologyMap f n x) :=
    DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (H.map_comp f t)) x
  have ht := TwistComparison.BigCrystallineTwistComparison.naturality p k B σ r hr hbase bF e
    (he).isDPMorphism he' hb n (HomologicalComplex.homologyMap f n x)
  have hg := AffineFrobeniusComparison.BigCrystallineAffineFrobeniusComparison.naturality p k B σ r hr hbase n x
  have hmap := congrArg
    (NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistCohomology.cohomologyMap (p := p) e (he).isDPMorphism he' hb n) hg
  have hf := FrobeniusFactorization.CrystallineFrobeniusFactorization.original p k X₀ g
    (AffineFrobeniusComparison.BigCrystallineAffineFrobeniusComparison.geometric_map p k B) hb n (v x)
  exact (congrArg (fun y => v (m y)) hc).trans (ht.trans (hmap.trans hf))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.AffineFrobeniusNaturality.BigCrystallineAffineFrobeniusNaturality

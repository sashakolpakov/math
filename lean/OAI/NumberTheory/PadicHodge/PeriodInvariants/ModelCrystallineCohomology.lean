import OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineFrobenius
import OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallinePullback
import OAI.NumberTheory.PadicHodge.PeriodInvariants.ResidueCoefficients

/-! # Model Crystalline Cohomology -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.ModelCrystallineCohomology

noncomputable section

/-!
# Crystalline cohomology of actual integral models

These are the crystalline Ext groups of the scheme-theoretic special
fiber. Their rational scalar field is the same constructed K_0 used for
D_cris. Frobenius is the actual p-semilinear operator, and each model
endomorphism induces pullback through the big crystalline site.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.PeriodInvariants.IntegralGeometry OAI.NumberTheory.PadicHodge.PeriodInvariants.ResidueCoefficients

variable (p : ℕ) [Fact p.Prime]
variable (K : Type u) [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable (M : IntegralGeometry.IntegralModel p K)

abbrev SpecialFiber := (IntegralGeometry.specialFiberFunctor p K).obj M

instance specialFiber_separated [IsSeparated M.hom] : IsSeparated (SpecialFiber p K M).hom := by
  change IsSeparated (pullback.snd M.hom
    (Scheme.Spec.map (CommRingCat.ofHom (IsLocalRing.residue (IntegralGeometry.ringOfIntegers p K))).op))
  infer_instance

abbrev IntegralCohomology (n : ℕ) :=
  IntegralComparison.Witt.Crystalline.integralCohomology p (IntegralGeometry.ResidueField p K) (SpecialFiber p K M) n

abbrev CrystallineCohomology (n : ℕ) :=
  IntegralComparison.Witt.Crystalline.rationalCohomology p (IntegralGeometry.ResidueField p K) (SpecialFiber p K M) n

variable [IsSeparated M.hom]

def crystallineFrobenius (n : ℕ) :
    CrystallineCohomology p K M n →ₛₗ[(ResidueCoefficients.coefficientFrobenius p K).toRingHom]
      CrystallineCohomology p K M n :=
  CrystallineFrobenius.rationalFrobenius p (IntegralGeometry.ResidueField p K) (SpecialFiber p K M) n

def integralEndomorphism (g : End M) (n : ℕ) :
    IntegralCohomology p K M n →ₗ[ResidueCoefficients.WittCoefficients p K] IntegralCohomology p K M n :=
  CrystallinePullback.integralPullback p (IntegralGeometry.ResidueField p K) ((IntegralGeometry.specialEndomorphism p K M) g) n

def crystallineEndomorphism (g : End M) (n : ℕ) :
    CrystallineCohomology p K M n →ₗ[ResidueCoefficients.K0 p K] CrystallineCohomology p K M n :=
  (integralEndomorphism p K M g n).baseChange (ResidueCoefficients.K0 p K)

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.ModelCrystallineCohomology

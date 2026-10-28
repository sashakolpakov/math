import OAI.NumberTheory.PadicHodge.PeriodInvariants.DcrisPullback
import OAI.NumberTheory.PadicHodge.PeriodInvariants.ModelCrystallineCohomology

/-! # Period Invariants -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.PeriodInvariants

noncomputable section

/-! The complete repaired PeriodInvariants proposition as an explicit comparison input. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.PeriodInvariants.IntegralGeometry OAI.NumberTheory.PadicHodge.PeriodInvariants.ResidueCoefficients OAI.NumberTheory.PadicHodge.PeriodInvariants.DcrisMem
  PeriodInvariants.ModelCrystallineCohomology

attribute [local instance] PeriodInvariants.DcrisMem.periodQpSMul PeriodInvariants.DcrisMem.periodQpModule
  PeriodInvariants.DcrisMem.periodQpMulAction PeriodInvariants.DcrisMem.periodK0Module PeriodInvariants.DcrisMem.tensorK0Module

local instance dcrisAddCommGroup (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
    (M : PeriodInvariants.IntegralGeometry.IntegralModel p K) (i : ℕ) : AddCommGroup (PeriodInvariants.DcrisMem.geometricDcris p K M i) :=
  Submodule.addCommGroup (R := PeriodInvariants.ResidueCoefficients.K0 p K)
    (M := TensorProduct ℚ_[p] (PeriodInvariants.PeriodRing.Bcris p) (PeriodInvariants.EtaleGalois.geometricEtaleCohomology p K M i))
    (module_M := PeriodInvariants.DcrisMem.tensorK0Module p K (V := PeriodInvariants.EtaleGalois.geometricEtaleCohomology p K M i))
    (PeriodInvariants.DcrisMem.geometricDcris p K M i)

local instance dcrisModule (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
    (M : PeriodInvariants.IntegralGeometry.IntegralModel p K) (i : ℕ) : Module (PeriodInvariants.ResidueCoefficients.K0 p K) (PeriodInvariants.DcrisMem.geometricDcris p K M i) :=
  PeriodInvariants.DcrisMem.geometricDcrisModule p K M i

/-- Full crystalline comparison, including actual Frobenius and every model endomorphism. -/
def CrystallineComparisonInput : Prop :=
  ∀
    (p : ℕ) [Fact p.Prime]
    (K : Type u) [Field K]
    [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
    (M : PeriodInvariants.IntegralGeometry.IntegralModel p K)
    [Smooth M.hom] [IsProper M.hom]
    (i : ℕ),
    FiniteDimensional ℚ_[p] (PeriodInvariants.EtaleGalois.geometricEtaleCohomology p K M i) ∧
      FiniteDimensional (PeriodInvariants.ResidueCoefficients.K0 p K) (PeriodInvariants.DcrisMem.geometricDcris p K M i) ∧
      FiniteDimensional (PeriodInvariants.ResidueCoefficients.K0 p K) (PeriodInvariants.ModelCrystallineCohomology.CrystallineCohomology p K M i) ∧
      Function.Bijective (PeriodInvariants.DcrisMem.geometricScalarExtension p K M i) ∧
      ∃ cmp : PeriodInvariants.DcrisMem.geometricDcris p K M i ≃ₗ[PeriodInvariants.ResidueCoefficients.K0 p K] PeriodInvariants.ModelCrystallineCohomology.CrystallineCohomology p K M i,
        (∀ x : PeriodInvariants.DcrisMem.geometricDcris p K M i,
          cmp (PeriodInvariants.DcrisMem.geometricDcrisFrobenius p K M i x) = PeriodInvariants.ModelCrystallineCohomology.crystallineFrobenius p K M i (cmp x)) ∧
        (∀ (f : End M) (x : PeriodInvariants.DcrisMem.geometricDcris p K M i),
          cmp (PeriodInvariants.DcrisPullback.geometricPullback p K f i x) =
            PeriodInvariants.ModelCrystallineCohomology.crystallineEndomorphism p K M f i (cmp x))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.PeriodInvariants

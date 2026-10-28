import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.GlobalFunctionResidue
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.CrystallineDegreeZeroTorsion
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.CrystallineFiniteness
import OAI.NumberTheory.PadicHodge.PeriodInvariants.PrincipalAdicLinearCriterion
import OAI.NumberTheory.PadicHodge.IntegralComparison.GlobalFunction.CrystallineGeneration

/-! # Crystalline Equivalence -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.GlobalFunction.CrystallineEquivalence

noncomputable section

/-! Actual Witt vectors of global functions identify with the original integral crystalline H⁰. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

attribute [local instance] PeriodInvariants.WittAlgebraFunctor.wittAlgebra PeriodInvariants.WittAlgebraFunctor.residueAlgebra

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom] [Nonempty X.left]
  (hprojective : Projectivity.Construction.ProjectiveOver k X.hom)

local notation "W" => WittVector p k
local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.GlobalFunctionAlgebra.algebra k X
local notation "M" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.integralCohomology p k X 0

include hprojective in
private theorem perfect : PerfectRing A p := by
  let := SmoothProper.GlobalFunctionAlgebra.nontrivial k X
  let := SmoothProper.GlobalFunctionAlgebra.module_finite k X hprojective
  let := SmoothProper.GlobalFunctionAlgebra.etale k X p hprojective
  exact PeriodInvariants.FiniteEtaleWittModule.targetPerfect p k A

theorem surjective : Function.Surjective (SmoothProper.GlobalFunctionConstants.integralMap p k X hprojective) :=
  CrystallineGeneration.surjective p k X hprojective

theorem reflects_prime (w : WittVector p A)
    (hw : ∃ y : M, (p : W) • y = SmoothProper.GlobalFunctionConstants.integralMap p k X hprojective w) :
    ∃ v : WittVector p A, (p : W) • v = w := by
  let := SmoothProper.GlobalFunctionAlgebra.characteristic k X p
  let := perfect p k X hprojective
  obtain ⟨y, hy⟩ := hw
  have hz : Crystalline.GlobalFunctionResidue.map p k X hprojective ((p : W) • y) = 0 := by
    rw [map_smul, Algebra.smul_def, map_natCast, CharP.cast_eq_zero A p, zero_mul]
  have hc : w.coeff 0 = 0 :=
    (Crystalline.GlobalFunctionResidue.constants p k X hprojective w).symm.trans
      ((congrArg (Crystalline.GlobalFunctionResidue.map p k X hprojective) hy.symm).trans hz)
  obtain ⟨v, hv⟩ := (Ideal.mem_span_singleton.mp ((WittVector.mem_span_p_iff_coeff_zero_eq_zero w).mpr hc))
  refine ⟨v, ?_⟩
  rw [Algebra.smul_def, map_natCast]
  exact hv.symm

theorem injective : Function.Injective (SmoothProper.GlobalFunctionConstants.integralMap p k X hprojective) := by
  let := SmoothProper.GlobalFunctionAlgebra.characteristic k X p
  let := perfect p k X hprojective
  let := PeriodInvariants.WittAlgebraCompleteness.complete p k A
  exact PeriodInvariants.PrincipalAdicLinearCriterion.injective (p : W)
    (SmoothProper.GlobalFunctionConstants.integralMap p k X hprojective)
    (SmoothProper.CrystallineDegreeZeroTorsion.regular p k X hprojective)
    (reflects_prime p k X hprojective)

def integralEquiv : WittVector p A ≃ₗ[W] M :=
  LinearEquiv.ofBijective (SmoothProper.GlobalFunctionConstants.integralMap p k X hprojective)
    ⟨injective p k X hprojective, surjective p k X hprojective⟩

def rationalEquiv : TensorProduct W (FractionRing W) (WittVector p A) ≃ₗ[FractionRing W]
    Witt.Crystalline.rationalCohomology p k X 0 :=
  (integralEquiv p k X hprojective).baseChange W (FractionRing W) (WittVector p A) M

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.GlobalFunction.CrystallineEquivalence

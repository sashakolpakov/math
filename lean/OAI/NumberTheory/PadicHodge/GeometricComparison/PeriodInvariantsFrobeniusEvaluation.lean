import OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineFrobenius

/-! # Period Invariants Frobenius Evaluation -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.PeriodInvariantsFrobeniusEvaluation.Crystalline

noncomputable section

/-! Evaluation of the native semilinear crystalline Frobenius before coefficient specialization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem e61BigFrobenius_apply (p : ℕ) [Fact p.Prime] (k : Type u)
    [Field k] [CharP k p] [PerfectRing k p]
    (X : Over (Spec (CommRingCat.of k))) (n : ℕ)
    (x : PeriodInvariants.CrystallineFrobenius.BigIntegralCohomology p k X n) :
    PeriodInvariants.CrystallineFrobenius.bigFrobenius p k X n x =
      PeriodInvariants.CrystallineTwistCohomology.cohomologyMap (WittVector.frobeniusEquiv p k)
        (IntegralComparison.Witt.Crystalline.wittFrobeniusDP p k).isDPMorphism
        (PeriodInvariants.WittFrobeniusGeometry.inverse_isDPMorphism p k)
        (PeriodInvariants.WittFrobeniusGeometry.schemeFrobenius_over p k X) n
        (IntegralComparison.BigCrystallineCohomology.pullback (PeriodInvariants.WittFrobeniusGeometry.schemeFrobenius p k X) rfl n x) := rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.PeriodInvariantsFrobeniusEvaluation.Crystalline

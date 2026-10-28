import OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineFrobenius

/-! # Frobenius Factorization -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.FrobeniusFactorization.CrystallineFrobeniusFactorization

noncomputable section

/-! # The original crystalline Frobenius through an identified geometric map -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p]
  (X : Over (Spec (CommRingCat.of k)))

theorem original (g : X.left ⟶ X.left)
    (hg : g = NumberTheory.PadicHodge.PeriodInvariants.WittFrobeniusGeometry.schemeFrobenius p k X)
    (h : g ≫ NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k X =
      NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k X ≫
        Spec.map (CommRingCat.ofHom (WittVector.frobeniusEquiv p k).toRingHom))
    (n : ℕ) (x : NumberTheory.PadicHodge.PeriodInvariants.CrystallineFrobenius.BigIntegralCohomology p k X n) :
    NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistCohomology.cohomologyMap (p := p)
      (δ := Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (WittVector.frobeniusEquiv p k)
      (NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittFrobeniusDP p k).isDPMorphism
      (NumberTheory.PadicHodge.PeriodInvariants.WittFrobeniusGeometry.inverse_isDPMorphism p k) h n
      (NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.pullback (p := p)
        (J := Ideal.span {(p : WittVector p k)}) (δ := Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
        (fY := NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k X) g rfl n x) =
    NumberTheory.PadicHodge.PeriodInvariants.CrystallineFrobenius.bigFrobenius p k X n x := by
  subst g
  rfl

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.FrobeniusFactorization.CrystallineFrobeniusFactorization

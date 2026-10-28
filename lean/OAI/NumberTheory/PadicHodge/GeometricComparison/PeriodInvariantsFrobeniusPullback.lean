import OAI.NumberTheory.PadicHodge.GeometricComparison.PeriodInvariantsFrobeniusEvaluation
import OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.TrivialTwistPullback
import OAI.NumberTheory.PadicHodge.GeometricComparison.PrimeFieldSchemeFrobenius
import OAI.NumberTheory.PadicHodge.GeometricComparison.WittFrobenius
import OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallinePullback

/-! # Period Invariants Frobenius Pullback -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.PeriodInvariantsFrobeniusPullback.Crystalline

noncomputable section

section

/-! PeriodInvariants's native semilinear Frobenius is the actual q-power scheme pullback at the split prime. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem bigPullback_congr {p : ℕ} {B : Type*} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
    {X Y : Scheme} {fX : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
    {g h : X ⟶ Y} (hg : g ≫ fY = fX) (hh : h ≫ fY = fX) (he : g = h)
    (n : ℕ) (x : IntegralComparison.BigCrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) fY n) :
    IntegralComparison.BigCrystallineCohomology.pullback g hg n x = IntegralComparison.BigCrystallineCohomology.pullback h hh n x := by
  subst h
  rfl

theorem e61BigFrobenius_eq_pullback (q : ℕ) [Fact q.Prime]
    (X : Over (Spec (CommRingCat.of (ZMod q)))) (n : ℕ)
    (x : PeriodInvariants.CrystallineFrobenius.BigIntegralCohomology q (ZMod q) X n) :
    PeriodInvariants.CrystallineFrobenius.bigFrobenius q (ZMod q) X n x =
      PeriodInvariants.CrystallinePullback.bigPullback q (ZMod q)
        (AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius (ZMod q) X) n x := by
  let g := PeriodInvariants.WittFrobeniusGeometry.schemeFrobenius q (ZMod q) X
  let f := IntegralComparison.Witt.Crystalline.wittStructureMap q (ZMod q) X
  let φ := WittVector.frobeniusEquiv q (ZMod q)
  have hg : g ≫ f = f := (congrArg (fun a => a ≫ f) (PrimeFieldSchemeFrobenius.Crystalline.schemeFrobenius_eq_finiteField q X)).trans
    (PeriodInvariants.CrystallinePullback.over_witt q (ZMod q) (AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius (ZMod q) X))
  have h := Crystalline.TrivialTwistPullback.CrystallineTwistIdentity.trivial_twist_after_pullback g hg φ
    (IntegralComparison.Witt.Crystalline.wittFrobeniusDP q (ZMod q)).isDPMorphism
    (PeriodInvariants.WittFrobeniusGeometry.inverse_isDPMorphism q (ZMod q)) (WittFrobenius.Crystalline.wittFrobenius_eq_id q)
    (PeriodInvariants.WittFrobeniusGeometry.schemeFrobenius_over q (ZMod q) X) n x
  have hp := bigPullback_congr hg
    (PeriodInvariants.CrystallinePullback.over_witt q (ZMod q) (AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius (ZMod q) X))
    (PrimeFieldSchemeFrobenius.Crystalline.schemeFrobenius_eq_finiteField q X) n x
  exact (PeriodInvariantsFrobeniusEvaluation.Crystalline.e61BigFrobenius_apply q (ZMod q) X n x).trans (h.trans hp)

end

/-! The actual integral and rational PeriodInvariants crystalline Frobenius equals ordinary q-power pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

variable (q : ℕ) [Fact q.Prime]
  (X : Over (Spec (CommRingCat.of (ZMod q)))) [IsSeparated X.hom]

theorem e61IntegralFrobenius_eq_pullback (n : ℕ)
    (x : IntegralComparison.Witt.Crystalline.integralCohomology q (ZMod q) X n) :
    PeriodInvariants.CrystallineFrobenius.integralFrobenius q (ZMod q) X n x =
      PeriodInvariants.CrystallinePullback.integralPullback q (ZMod q)
        (AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius (ZMod q) X) n x :=
  congrArg (IntegralComparison.Global.Crystalline.Comparison.integralEquivWitt q (ZMod q) X n)
    (e61BigFrobenius_eq_pullback q X n
      ((IntegralComparison.Global.Crystalline.Comparison.integralEquivWitt q (ZMod q) X n).symm x))

theorem e61RationalFrobenius_eq_pullback (n : ℕ)
    (x : IntegralComparison.Witt.Crystalline.rationalCohomology q (ZMod q) X n) :
    PeriodInvariants.CrystallineFrobenius.rationalFrobenius q (ZMod q) X n x =
      PeriodInvariants.CrystallinePullback.rationalPullback q (ZMod q)
        (AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius (ZMod q) X) n x := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    have hσ : PeriodInvariants.CrystallineFrobenius.scalarFrobenius q (ZMod q) a = a :=
      DFunLike.congr_fun (WittFrobenius.Crystalline.fractionFrobenius_eq_id q) a
    exact (PeriodInvariants.CrystallineFrobenius.rationalFrobenius_tmul q (ZMod q) X n a x).trans
      (congrArg₂ (fun b y => b ⊗ₜ[Crystalline.CoefficientAdapter.Witt q] y) hσ (e61IntegralFrobenius_eq_pullback q X n x))
  | add x y hx hy =>
    exact ((PeriodInvariants.CrystallineFrobenius.rationalFrobenius q (ZMod q) X n).map_add x y).trans
      ((congrArg₂ (fun a b => a + b) hx hy).trans
        ((PeriodInvariants.CrystallinePullback.rationalPullback q (ZMod q)
          (AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius (ZMod q) X) n).map_add x y).symm)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.PeriodInvariantsFrobeniusPullback.Crystalline

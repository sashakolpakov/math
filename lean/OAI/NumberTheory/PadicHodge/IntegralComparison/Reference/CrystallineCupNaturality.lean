import OAI.NumberTheory.PadicHodge.IntegralComparison.Rational.CrystallineCupNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.FrobeniusPullback

/-! # Crystalline Cup Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Reference.CrystallineCupNaturality

noncomputable section

/-! The actual rational crystalline cup is preserved by the original
geometric pullback and by the original finite-field Frobenius operator. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X Y : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]
  [IsProper Y.hom] [Smooth Y.hom] (g : X ⟶ Y)

omit [Fintype k] [Smooth X.hom] [Smooth Y.hom] in
/-- The native cup pullback has the exact original Witt-linear action. -/
theorem integralPullback_eq (i : ℕ) :
    Rational.CrystallineCupNaturality.integralPullback p k X Y g i =
      PeriodInvariants.CrystallinePullback.integralPullback p k g i := by
  ext x
  rfl

omit [Fintype k] [Smooth X.hom] [Smooth Y.hom] in
/-- Scalar extension retains the exact original rational pullback. -/
theorem pullback_eq (i : ℕ) :
    Rational.CrystallineCupNaturality.pullback p k X Y g i =
      PeriodInvariants.CrystallinePullback.rationalPullback p k g i :=
  congrArg (fun f => f.baseChange (FractionRing (WittVector p k)))
    (integralPullback_eq p k X Y g i)

variable (hX : Projectivity.Construction.ProjectiveOver k X.hom) (hY : Projectivity.Construction.ProjectiveOver k Y.hom)

theorem cup_natural (i j : ℕ) (x : Witt.Crystalline.rationalCohomology p k Y i)
    (y : Witt.Crystalline.rationalCohomology p k Y j) :
    PeriodInvariants.CrystallinePullback.rationalPullback p k g (i + j)
        (Rational.CrystallineCup.cup p k Y hY i j x y) =
      Rational.CrystallineCup.cup p k X hX i j
        (PeriodInvariants.CrystallinePullback.rationalPullback p k g i x)
        (PeriodInvariants.CrystallinePullback.rationalPullback p k g j y) := by
  rw [← pullback_eq p k X Y g (i + j), ← pullback_eq p k X Y g i,
    ← pullback_eq p k X Y g j]
  exact Rational.CrystallineCupNaturality.cup_natural p k X Y g hX hY i j x y

omit Y g hY in
theorem frobenius_cup (a : ℕ) (hcard : Fintype.card k = p ^ a)
    (i j : ℕ) (x : Witt.Crystalline.rationalCohomology p k X i) (y : Witt.Crystalline.rationalCohomology p k X j) :
    Global.CrystallineFrobenius.rationalFrobenius p k X a hcard (i + j)
        (Rational.CrystallineCup.cup p k X hX i j x y) =
      Rational.CrystallineCup.cup p k X hX i j
        (Global.CrystallineFrobenius.rationalFrobenius p k X a hcard i x)
        (Global.CrystallineFrobenius.rationalFrobenius p k X a hcard j y) := by
  rw [FrobeniusPullback.Q.rational, FrobeniusPullback.Q.rational,
    FrobeniusPullback.Q.rational]
  exact cup_natural p k X X (FrobeniusPullback.Q.endomorphism p k X a hcard) hX hX i j x y

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Reference.CrystallineCupNaturality

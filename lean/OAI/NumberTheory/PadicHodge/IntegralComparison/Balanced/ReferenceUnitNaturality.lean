import OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.RationalCupUnit
import OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.WittUnitNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.ReferenceCupNaturality

/-! # Reference Unit Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.ReferenceUnitNaturality.Reference

noncomputable section

/-! The original crystalline pullback and Frobenius preserve the actual
balanced coefficient-one class, at integral and rational level. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X Y : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]
  [IsProper Y.hom] [Smooth Y.hom] (g : X ⟶ Y)
  (hX : Projectivity.Construction.ProjectiveOver k X.hom) (hY : Projectivity.Construction.ProjectiveOver k Y.hom)

theorem integral_one : Integral.CrystallineCupNaturality.pullback p k X Y g 0
      (CupUnit.Integral.one p k Y hY) = CupUnit.Integral.one p k X hX := by
  apply CupAlgebra.Integral.ext p k X hX 0
  intro n
  rw [CupNaturality.Integral.restriction_pullback,
    CupUnit.Integral.restriction_one, CupUnit.Integral.restriction_one]
  exact WittUnitNaturality.one_natural p k X Y g n

theorem one_natural : PeriodInvariants.CrystallinePullback.rationalPullback p k g 0
      (RationalCupUnit.one p k Y hY) = RationalCupUnit.one p k X hX := by
  rw [← Reference.CrystallineCupNaturality.pullback_eq p k X Y g 0]
  exact (Rational.CrystallineCupNaturality.pullback_tmul p k X Y g 0 1
    (CupUnit.Integral.one p k Y hY)).trans
    (congrArg (fun z => (1 : FractionRing (WittVector p k)) ⊗ₜ[WittVector p k] z)
      ((Rational.CrystallineCupNaturality.integralPullback_apply p k X Y g 0 _).trans
        (integral_one p k X Y g hX hY)))

omit Y g hY in
theorem frobenius_one (a : ℕ) (hcard : Fintype.card k = p ^ a) :
    Global.CrystallineFrobenius.rationalFrobenius p k X a hcard 0
      (RationalCupUnit.one p k X hX) = RationalCupUnit.one p k X hX := by
  rw [FrobeniusPullback.Q.rational]
  exact one_natural p k X X (FrobeniusPullback.Q.endomorphism p k X a hcard) hX hX

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.ReferenceUnitNaturality.Reference

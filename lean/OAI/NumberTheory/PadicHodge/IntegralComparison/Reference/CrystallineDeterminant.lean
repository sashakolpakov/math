import OAI.NumberTheory.PadicHodge.IntegralComparison.Reference.ScalarCupCompatibility
import OAI.NumberTheory.PadicHodge.IntegralComparison.Reference.ScalarCupNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.GradedExteriorCup
import OAI.NumberTheory.PadicHodge.IntegralComparison.ScalarIntrinsicEndomorphismDeterminant

/-! # Crystalline Determinant -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Reference.CrystallineDeterminant

noncomputable section

/-! The determinant of an original crystalline pullback is its scalar
on the nonzero top exterior cup. The unit and product compatibilities
are supplied by the checked native crystalline constructions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]
  (hX : Projectivity.Construction.ProjectiveOver k X.hom)

local notation "F" => FractionRing (WittVector p k)
local notation "D" => OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.RationalCupUnit.data p k X hX
local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.rationalCohomology p k X

local notation "N" => Module.finrank (FractionRing (WittVector p k))
  (TensorProduct (WittVector p k) (FractionRing (WittVector p k))
    (Witt.Crystalline.integralCohomology p k X 1))

attribute [local irreducible] Balanced.RationalCrystallineCup.integralCup

attribute [local irreducible] GradedExteriorCup.exteriorPowerCup Module.finrank

variable [FiniteDimensional (FractionRing (WittVector p k))
  (Witt.Crystalline.rationalCohomology p k X 1)]

theorem of_top_scalar (f : X ⟶ X) (c : F)
    (hprod : GradedExteriorCup.exteriorPowerCup D N ≠ 0)
    (htop : ∀ x : H N, PeriodInvariants.CrystallinePullback.rationalPullback p k f N x = c • x) :
    (PeriodInvariants.CrystallinePullback.rationalPullback p k f 1).det = c := by
  let : FiniteDimensional F (TensorProduct (WittVector p k) F
      (Witt.Crystalline.integralCohomology p k X 1)) :=
    inferInstanceAs (FiniteDimensional F (H 1))
  have hu := ScalarCupCompatibility.unit p k X hX f
  have hc := ScalarCupNaturality.natural p k X hX f
  unfold PeriodInvariants.CrystallinePullback.rationalPullback at hu htop ⊢
  dsimp only [ScalarCupNaturality.endomorphism] at hc
  dsimp only [Witt.Crystalline.rationalCohomology, ModuleCat.of] at hu htop ⊢
  exact ScalarIntrinsicEndomorphismDeterminant.Intrinsic.det_eq_of_top_scalar F
    (Witt.Crystalline.integralCohomology p k X)
    (Balanced.RationalCrystallineCup.integralCup p k X hX)
    (Balanced.CupUnit.Integral.one p k X hX)
    (Balanced.RationalCupUnit.scalarLeft p k X hX)
    (Balanced.RationalCupUnit.scalarRight p k X hX)
    (Balanced.RationalCupUnit.scalarAssoc p k X hX)
    (Balanced.RationalCupUnit.scalarSquare p k X hX)
    (fun n => (PeriodInvariants.CrystallinePullback.integralPullback p k f n).baseChange F)
    (by exact hu)
    (by intro i j x y; exact hc i j x y)
    c (by exact hprod)
    (by intro x; exact htop x)

theorem of_trace (f : X ⟶ X) (c : F)
    (hprod : GradedExteriorCup.exteriorPowerCup D N ≠ 0)
    (trace : H N ≃ₗ[F] F)
    (htrace : ∀ x : H N, trace (PeriodInvariants.CrystallinePullback.rationalPullback p k f N x) = c * trace x) :
    (PeriodInvariants.CrystallinePullback.rationalPullback p k f 1).det = c := by
  apply of_top_scalar p k X hX f c hprod
  intro x
  apply trace.injective
  rw [htrace, map_smul]
  rfl

theorem of_additive_trace {T : Type*} [AddCommGroup T] (f : X ⟶ X) (d : ℕ)
    (hprod : GradedExteriorCup.exteriorPowerCup D N ≠ 0)
    (trace : H N →+ T) (hinj : Function.Injective trace)
    (htrace : ∀ x : H N, trace (PeriodInvariants.CrystallinePullback.rationalPullback p k f N x) = d • trace x) :
    (PeriodInvariants.CrystallinePullback.rationalPullback p k f 1).det = (d : F) := by
  apply of_top_scalar p k X hX f (d : F) hprod
  intro x
  apply hinj
  rw [htrace, Nat.cast_smul_eq_nsmul, map_nsmul]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Reference.CrystallineDeterminant

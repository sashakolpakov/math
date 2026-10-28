import OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.BettiSheafCompatibility
import OAI.AlgebraicGeometry.DivisorClass.Chern.LogCech

/-! # Log Integral Sheaf -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.LogIntegralSheaf

noncomputable section

/-! The original logarithmic singular class is the rationalization of its actual integer defect. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.DivisorClass.Chern.LogCech.RationalCech

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}} {I : Type} (U : I → Opens X)
  (l : LogCech.RationalCech.LogCechCochain X U) (h : LogCech.RationalCech.ExponentialCocycle X U l)

def logarithmicIntegerCech : Cech.IntegralRefinement.IntegerCechCochain U 2 :=
  fun a => ⟨fun x => Logarithms.Construction.logarithmicDefect
      (LogCech.RationalCech.edgeLog X U l 2 a x) (LogCech.RationalCech.edgeLog X U l 0 a x) (LogCech.RationalCech.edgeLog X U l 1 a x) (h a x),
    Logarithms.Construction.isLocallyConstant_logarithmicDefect
      (LogCech.RationalCech.edgeLog X U l 2 a) (LogCech.RationalCech.edgeLog X U l 0 a) (LogCech.RationalCech.edgeLog X U l 1 a) (h a)⟩

theorem logarithmicIntegerCech_rationalize :
    Cech.IntegralRefinement.integerCechRationalize U 2 (logarithmicIntegerCech U l h) = LogCech.RationalCech.logDefectCech X U l h := rfl

theorem logarithmicIntegerCech_closed :
    Cech.IntegralRefinement.integerCechDelta U 2 (logarithmicIntegerCech U l h) = 0 := by
  apply Cech.IntegralRefinement.integerCechRationalize_injective U 3
  rw [Cech.IntegralRefinement.integerCechRationalize_delta, logarithmicIntegerCech_rationalize, map_zero]
  exact LogCech.RationalCech.logDefectCech_closed X U l h

def logarithmicIntegralSheafClass (hU : ⨆ i, U i = ⊤) :
    CategoryTheory.Sheaf.H (IntegralConstantSheaf.integralConstantSheaf X) 2 :=
  IntegralCechSheaf.integerCechSheafClass U hU 1 (logarithmicIntegerCech U l h)
    (logarithmicIntegerCech_closed U l h)

variable [MetrizableSpace X] [StronglyLocallyContractibleSpace X] [LocallyPathConnectedSpace X]

theorem logarithmicIntegralSheafClass_rationalize
    (hU : ∀ x : X, ∃ i, x ∈ U i) :
    CategoryTheory.Sheaf.H.map (Rational.HolomorphicPeriod.integralToRationalConstantSheaf X) 2
      (logarithmicIntegralSheafClass U l h (Cech.BettiSheafCompatibility.cechCover_iSup_eq_top U hU)) =
        Rational.BettiCechSheafComparison.rationalBettiCechSheafEquiv X 1 (LogCech.RationalCech.logarithmicSingularClass X U hU l h) := by
  unfold logarithmicIntegralSheafClass
  rw [IntegralCechSheaf.integerCechSheafClass_rationalize]
  exact Cech.BettiSheafCompatibility.rationalCechSheafClass_eq_betti U hU (Cech.BettiSheafCompatibility.cechCover_iSup_eq_top U hU)
    (LogCech.RationalCech.logDefectCocycle X U l h)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.LogIntegralSheaf

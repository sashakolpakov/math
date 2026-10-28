import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.LogTransition
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.LogIntegralBoundary

/-! # Intrinsic Log Cochains -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.IntrinsicLogCochains

noncomputable section

/-! The original logarithm, unit transition, and integer defect in native Cech coordinates. -/

open _root_.CategoryTheory _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
  (M : Type) [TopologicalSpace M] [ChartedSpace E M] [CompactSpace M] [NormalSpace M]

def holomorphicNativeLogCochain (u : Connecting.holomorphicUnitCohomology E M) :
    ((CategoryTheory.cechComplexFunctor (Singular.holomorphicLogCover E M u)).obj
      (Sheaves.holomorphicFunctionSheaf E M).obj).X 1 :=
  (Abelian.CechCoordinates.abelianCechCoordinates (Sheaves.holomorphicFunctionSheaf E M).obj (Singular.holomorphicLogCover E M u) 1).symm
    (CechForget.holomorphicCechOfLog E M (Singular.holomorphicLogCover E M u) (Singular.holomorphicLogCech E M u)
      (ChernSheaf.holomorphicLogCech_holomorphic E M u))

def holomorphicNativeUnitTransition (u : Connecting.holomorphicUnitCohomology E M) :
    ((CategoryTheory.cechComplexFunctor (Singular.holomorphicLogCover E M u)).obj
      (Sheaves.holomorphicUnitsSheaf E M).obj).X 1 :=
  (Abelian.CechCoordinates.abelianCechCoordinates (Sheaves.holomorphicUnitsSheaf E M).obj (Singular.holomorphicLogCover E M u) 1).symm
    (LogTransition.holomorphicLogTransitionCech E M u)

def holomorphicNativeIntegerDefect (u : Connecting.holomorphicUnitCohomology E M) :
    ((CategoryTheory.cechComplexFunctor (Singular.holomorphicLogCover E M u)).obj
      (IntegralConstantSheaf.integralConstantSheaf (TopCat.of M)).obj).X 2 :=
  (Abelian.CechCoordinates.abelianCechCoordinates (IntegralConstantSheaf.integralConstantSheaf (TopCat.of M)).obj (Singular.holomorphicLogCover E M u) 2).symm
    (LogIntegralSheaf.logarithmicIntegerCech (X := TopCat.of M) (Singular.holomorphicLogCover E M u) (Singular.holomorphicLogCech E M u)
      (Singular.holomorphicLogCech_cocycle E M u))

theorem holomorphicNativeIntegerDefect_closed (u : Connecting.holomorphicUnitCohomology E M) :
    ((CategoryTheory.cechComplexFunctor (Singular.holomorphicLogCover E M u)).obj
      (IntegralConstantSheaf.integralConstantSheaf (TopCat.of M)).obj).d 2 3 (holomorphicNativeIntegerDefect E M u) = 0 :=
  Abelian.CechClasses.abelianCechNative_closed (X := TopCat.of M) (Singular.holomorphicLogCover E M u)
    (IntegralConstantSheaf.integralConstantSheaf (TopCat.of M)).obj 2 _
    (LogIntegralSheaf.logarithmicIntegerCech_closed (X := TopCat.of M) (Singular.holomorphicLogCover E M u)
      (Singular.holomorphicLogCech E M u) (Singular.holomorphicLogCech_cocycle E M u))

theorem holomorphicNativeLogCochain_period (u : Connecting.holomorphicUnitCohomology E M) :
    ((CategoryTheory.cechComplexFunctor (Singular.holomorphicLogCover E M u)).map
      (PeriodSequence.holomorphicPeriodSheafMap E M).hom).f 2 (holomorphicNativeIntegerDefect E M u) =
      ((CategoryTheory.cechComplexFunctor (Singular.holomorphicLogCover E M u)).obj
        (Sheaves.holomorphicFunctionSheaf E M).obj).d 1 2 (holomorphicNativeLogCochain E M u) := by
  let U := Singular.holomorphicLogCover E M u
  let l := CechForget.holomorphicCechOfLog E M U (Singular.holomorphicLogCech E M u) (ChernSheaf.holomorphicLogCech_holomorphic E M u)
  have hc := Cech.IntrinsicOperators.abelianCechCoordinates_symm_coefficient (X := TopCat.of M)
    (F := (IntegralConstantSheaf.integralConstantSheaf (TopCat.of M)).obj) (G := (Sheaves.holomorphicFunctionSheaf E M).obj)
    U (PeriodSequence.holomorphicPeriodSheafMap E M).hom 2
    (LogIntegralSheaf.logarithmicIntegerCech (X := TopCat.of M) U (Singular.holomorphicLogCech E M u) (Singular.holomorphicLogCech_cocycle E M u))
  have hd := Cech.IntrinsicOperators.abelianCechCoordinates_symm_d (X := TopCat.of M) U (Sheaves.holomorphicFunctionSheaf E M).obj 1 l
  have hb := LogIntegralBoundary.holomorphicLogCech_integral_boundary E M U (Singular.holomorphicLogCech E M u)
    (Singular.holomorphicLogCech_cocycle E M u) (ChernSheaf.holomorphicLogCech_holomorphic E M u)
  exact hc.trans ((congrArg (Abelian.CechCoordinates.abelianCechCoordinates (Sheaves.holomorphicFunctionSheaf E M).obj U 2).symm
    hb.symm).trans hd.symm)

theorem holomorphicNativeLogCochain_exponential (u : Connecting.holomorphicUnitCohomology E M) :
    ((CategoryTheory.cechComplexFunctor (Singular.holomorphicLogCover E M u)).map
      (Sheaves.holomorphicExponentialSheafMap E M).hom).f 1 (holomorphicNativeLogCochain E M u) =
      holomorphicNativeUnitTransition E M u := by
  have hc := Cech.IntrinsicOperators.abelianCechCoordinates_symm_coefficient (X := TopCat.of M)
    (F := (Sheaves.holomorphicFunctionSheaf E M).obj) (G := (Sheaves.holomorphicUnitsSheaf E M).obj)
    (Singular.holomorphicLogCover E M u) (Sheaves.holomorphicExponentialSheafMap E M).hom 1
    (CechForget.holomorphicCechOfLog E M (Singular.holomorphicLogCover E M u) (Singular.holomorphicLogCech E M u)
      (ChernSheaf.holomorphicLogCech_holomorphic E M u))
  exact hc.trans (congrArg
    (Abelian.CechCoordinates.abelianCechCoordinates (Sheaves.holomorphicUnitsSheaf E M).obj (Singular.holomorphicLogCover E M u) 1).symm
    (LogTransition.holomorphicLogTransitionCech_exponential E M u))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.IntrinsicLogCochains

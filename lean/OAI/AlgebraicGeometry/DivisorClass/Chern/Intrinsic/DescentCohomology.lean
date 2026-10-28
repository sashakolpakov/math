import OAI.AlgebraicGeometry.DivisorClass.Chern.Intrinsic.SingularBoundary
import OAI.AlgebraicGeometry.DivisorClass.Chern.Singular.Gamma
import OAI.AlgebraicGeometry.DivisorClass.Chern.FlasqueCechCoefficients
import OAI.AlgebraicGeometry.DivisorClass.Chern.IntegralCechSheaf

/-! # Descent Cohomology -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! The descended rational Cech class agrees with the actual Betti-to-sheaf class. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.TopCat.Sheaf
open OAI.AlgebraicGeometry.SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}} {I : Type} (U : I → Opens X)

theorem Intrinsic.DescentCohomology.rationalCechCocycle_closed (n : ℕ)
    (k : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (Rational.Cech.RationalCech.cechComplex (Cech.Obj.RationalCech.locallyConstantPresheaf X) U) (n + 1)) :
    Rational.Cech.RationalCech.cechDelta (Cech.Obj.RationalCech.locallyConstantPresheaf X) U (n + 1) k.val = 0 := by
  have h := k.property
  erw [AlgebraicTopology.Cohomology.Singular.Representatives.mem_cochainCocycles_iff, Rational.Cech.RationalCech.cechComplex_d] at h
  exact h

def Intrinsic.DescentCohomology.rationalNativeCechClass (n : ℕ)
    (k : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (Rational.Cech.RationalCech.cechComplex (Cech.Obj.RationalCech.locallyConstantPresheaf X) U) (n + 1)) :
    ((CategoryTheory.cechComplexFunctor U).obj (Rational.HolomorphicPeriod.rationalConstantAbelianSheaf X).obj).homology (n + 1) :=
  Abelian.CechClasses.abelianCechNativeClass U (Rational.HolomorphicPeriod.rationalConstantAbelianSheaf X).obj n k.val
    ((IntegralCechSheaf.rationalCechAbelianDelta U (n + 1) k.val).trans (Intrinsic.DescentCohomology.rationalCechCocycle_closed U n k))

theorem Intrinsic.DescentCohomology.abelianCochainMap_closed {A B : CochainComplex AddCommGrpCat.{0} ℕ}
    (f : A ⟶ B) (n : ℕ) (x : A.X (n + 1)) (hx : A.d (n + 1) (n + 2) x = 0) :
    B.d (n + 1) (n + 2) (f.f (n + 1) x) = 0 := by
  have h := ConcreteCategory.congr_hom (f.comm (n + 1) (n + 2)) x
  simpa only [ConcreteCategory.comp_apply, hx, map_zero] using h

variable {U} {c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of ℚ ℚ) X 2} (d : Singular.CechDescent.SingularCechDescentData c U)
  (k : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (Rational.Cech.RationalCech.cechComplex (Cech.Obj.RationalCech.locallyConstantPresheaf X) U) 2)
  (hk : Cech.Obj.RationalCech.locallyConstantCechEvaluation X U 2 k.val =
    -Rational.Cech.RationalCech.cechDelta ((AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X).X 0) U 1 d.horizontal)

include hk in
theorem Singular.CechDescent.SingularCechDescentData.native_total_class :
    HomologicalComplex.homologyMap
        (FlasqueCechD.abelianCechVerticalEdge U (Abelian.SingularAugmentation.rationalAbelianConstantAugmentation X)
          (Abelian.SingularAugmentation.rationalAbelianConstantAugmentation_d X)) 2 (Intrinsic.DescentCohomology.rationalNativeCechClass U 1 k) =
      HomologicalComplex.homologyMap
        (FlasqueCechD.abelianCechHorizontalEdge U (Rational.BettiSheafComparison.rationalAbelianSingularResolution X)) 2
          (Singular.Gamma.rationalSingularGammaClass X 1 c) := by
  let v := FlasqueCechD.abelianCechVerticalEdge U (Abelian.SingularAugmentation.rationalAbelianConstantAugmentation X)
    (Abelian.SingularAugmentation.rationalAbelianConstantAugmentation_d X)
  let h := FlasqueCechD.abelianCechHorizontalEdge U (Rational.BettiSheafComparison.rationalAbelianSingularResolution X)
  let x := (Abelian.CechCoordinates.abelianCechCoordinates (Rational.HolomorphicPeriod.rationalConstantAbelianSheaf X).obj U 2).symm k.val
  have hx := Abelian.CechClasses.abelianCechNative_closed U (Rational.HolomorphicPeriod.rationalConstantAbelianSheaf X).obj 2 k.val
    ((IntegralCechSheaf.rationalCechAbelianDelta U 2 k.val).trans (Intrinsic.DescentCohomology.rationalCechCocycle_closed U 1 k))
  have hy := Singular.Gamma.rationalSingularToGamma_closed X 1 c
  have hv := Intrinsic.DescentCohomology.abelianCochainMap_closed v 1 x hx
  have hh := Intrinsic.DescentCohomology.abelianCochainMap_closed h 1 ((Singular.GammaAugmentation.rationalSingularToGamma X).f 2 c.val) hy
  unfold Intrinsic.DescentCohomology.rationalNativeCechClass Abelian.CechClasses.abelianCechNativeClass Singular.Gamma.rationalSingularGammaClass
  rw [SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.homologyMap_abCyclesMk 1 v x hx hv,
    SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.homologyMap_abCyclesMk 1 h ((Singular.GammaAugmentation.rationalSingularToGamma X).f 2 c.val) hy hh]
  exact SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.homologyπ_cyclesMk_eq_of_sub_eq_boundary 1 _ _ _ hv hh d.nativeTotalPrimitive
    (d.nativeTotalPrimitive_d k hk).symm

include hk in
theorem Singular.CechDescent.SingularCechDescentData.native_gamma_class [MetrizableSpace X] (hU : ⨆ i, U i = ⊤) :
    FlasqueCechD.abelianCechFlasqueComparison U (Rational.BettiSheafComparison.rationalAbelianSingularResolution_flasque X)
        (Abelian.SingularAugmentation.rationalAbelianConstantAugmentation X) (Abelian.SingularAugmentation.rationalAbelianConstantAugmentation_d X) hU 1
          (Intrinsic.DescentCohomology.rationalNativeCechClass U 1 k) = Singular.Gamma.rationalSingularGammaClass X 1 c := by
  change (FlasqueCechD.abelianFlasqueCechHomologyIso U (Rational.BettiSheafComparison.rationalAbelianSingularResolution X)
      (Rational.BettiSheafComparison.rationalAbelianSingularResolution_flasque X) hU 1).inv
    (HomologicalComplex.homologyMap
      (FlasqueCechD.abelianCechVerticalEdge U (Abelian.SingularAugmentation.rationalAbelianConstantAugmentation X)
        (Abelian.SingularAugmentation.rationalAbelianConstantAugmentation_d X)) 2 (Intrinsic.DescentCohomology.rationalNativeCechClass U 1 k)) = _
  rw [d.native_total_class k hk]
  exact (FlasqueCechD.abelianFlasqueCechHomologyIso U (Rational.BettiSheafComparison.rationalAbelianSingularResolution X)
    (Rational.BettiSheafComparison.rationalAbelianSingularResolution_flasque X) hU 1).hom_inv_id_apply _

include hk in
theorem Singular.CechDescent.SingularCechDescentData.native_sheaf_class [MetrizableSpace X]
    [StronglyLocallyContractibleSpace X] [LocallyPathConnectedSpace X] (hU : ⨆ i, U i = ⊤) :
    Abelian.CechComparison.abelianCechToSheaf U (Rational.HolomorphicPeriod.rationalConstantAbelianSheaf X) hU 1 (Intrinsic.DescentCohomology.rationalNativeCechClass U 1 k) =
      Rational.BettiCechSheafComparison.rationalBettiCechSheafEquiv X 1 (AlgebraicTopology.Cohomology.Singular.Representatives.singularClass (ModuleCat.of ℚ ℚ) X 2 c) := by
  let e := Rational.BettiSheafComparison.rationalConstantAbelianZeroIso X
  let C := GammaSectionsComparison.nativeFlasqueCohomologyIsoOfZero (Rational.BettiSheafComparison.rationalAbelianSingularResolution X)
    (Rational.BettiSheafComparison.rationalAbelianSingularResolution_flasque X) (Rational.BettiSheafComparison.rationalAbelianSingularResolution_exact X) 1 e
  have hm : FlasqueCechD.abelianCechFlasqueComparison U (Rational.BettiSheafComparison.rationalAbelianSingularResolution_flasque X)
        (Abelian.SingularAugmentation.rationalAbelianConstantAugmentation X) (Abelian.SingularAugmentation.rationalAbelianConstantAugmentation_d X) hU 1 ≫ C.hom =
      Abelian.CechComparison.abelianCechToSheaf U (Rational.HolomorphicPeriod.rationalConstantAbelianSheaf X) hU 1 := by
    have ha : (e.hom ≫ (HodgeConjecture.DegreeTwo.ThomGoodShiftFlasque.Constructions.cochainZeroHomologyAugmentation (Rational.BettiSheafComparison.rationalAbelianSingularResolution X)).f 0) ≫
        (Rational.BettiSheafComparison.rationalAbelianSingularResolution X).d 0 1 = 0 := by
      rw [Abelian.SingularAugmentation.rationalAbelianConstantAugmentation_zeroIso]
      exact Abelian.SingularAugmentation.rationalAbelianConstantAugmentation_d X
    have he := FlasqueCechCoefficients.nativeFlasqueCohomologyIsoOfZero_cech U
      (Rational.BettiSheafComparison.rationalAbelianSingularResolution_flasque X) (Rational.BettiSheafComparison.rationalAbelianSingularResolution_exact X) e ha hU 1
    simpa only [e, Abelian.SingularAugmentation.rationalAbelianConstantAugmentation_zeroIso] using he
  have hclass := ConcreteCategory.congr_hom hm (Intrinsic.DescentCohomology.rationalNativeCechClass U 1 k)
  change C.hom (FlasqueCechD.abelianCechFlasqueComparison U (Rational.BettiSheafComparison.rationalAbelianSingularResolution_flasque X)
    (Abelian.SingularAugmentation.rationalAbelianConstantAugmentation X) (Abelian.SingularAugmentation.rationalAbelianConstantAugmentation_d X) hU 1
      (Intrinsic.DescentCohomology.rationalNativeCechClass U 1 k)) = _ at hclass
  rw [d.native_gamma_class k hk hU] at hclass
  exact hclass.symm.trans (Singular.Gamma.rationalBettiCechSheafEquiv_class X 1 c).symm

end

end OAI.AlgebraicGeometry.DivisorClass.Chern

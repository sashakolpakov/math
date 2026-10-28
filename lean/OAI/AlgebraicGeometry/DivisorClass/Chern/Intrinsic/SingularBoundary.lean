import OAI.AlgebraicGeometry.DivisorClass.Chern.Abelian.SingularAugmentation
import OAI.AlgebraicGeometry.DivisorClass.Chern.Singular.GammaAugmentation
import OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.IntrinsicOperators

/-! # Singular Boundary -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

section

/-! The actual singular descent data in the native singular-sheaf Cech double complex. -/

open _root_.CategoryTheory _root_.TopologicalSpace _root_.TopCat.Sheaf

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}} {I : Type} {U : I → Opens X}
  {c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of ℚ ℚ) X 2} (d : Singular.CechDescent.SingularCechDescentData c U)

def Singular.CechDescent.SingularCechDescentData.nativeHorizontal :
    ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex U (Rational.BettiSheafComparison.rationalAbelianSingularResolution X)).X 0).X 1 :=
  (Abelian.CechCoordinates.abelianCechCoordinates ((Rational.BettiSheafComparison.rationalAbelianSingularResolution X).X 0).obj U 1).symm
    (Singular.CechSheafification.singularCechSheafify U 0 1 d.horizontal)

def Singular.CechDescent.SingularCechDescentData.nativeVertical :
    ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex U (Rational.BettiSheafComparison.rationalAbelianSingularResolution X)).X 1).X 0 :=
  (Abelian.CechCoordinates.abelianCechCoordinates ((Rational.BettiSheafComparison.rationalAbelianSingularResolution X).X 1).obj U 0).symm
    (Singular.CechSheafification.singularCechSheafify U 1 0 d.vertical)

theorem Singular.CechDescent.SingularCechDescentData.native_middle :
    ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex U (Rational.BettiSheafComparison.rationalAbelianSingularResolution X)).d 0 1).f 1 d.nativeHorizontal =
      ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex U (Rational.BettiSheafComparison.rationalAbelianSingularResolution X)).X 1).d 0 1 d.nativeVertical := by
  change ((CategoryTheory.cechComplexFunctor U).map
      ((Rational.BettiSheafComparison.rationalAbelianSingularResolution X).d 0 1).hom).f 1
        ((Abelian.CechCoordinates.abelianCechCoordinates ((Rational.BettiSheafComparison.rationalAbelianSingularResolution X).X 0).obj U 1).symm
          (Singular.CechSheafification.singularCechSheafify U 0 1 d.horizontal)) =
    ((CategoryTheory.cechComplexFunctor U).obj ((Rational.BettiSheafComparison.rationalAbelianSingularResolution X).X 1).obj).d 0 1
      ((Abelian.CechCoordinates.abelianCechCoordinates ((Rational.BettiSheafComparison.rationalAbelianSingularResolution X).X 1).obj U 0).symm
        (Singular.CechSheafification.singularCechSheafify U 1 0 d.vertical))
  rw [Cech.IntrinsicOperators.abelianCechCoordinates_symm_coefficient, Cech.IntrinsicOperators.abelianCechCoordinates_symm_d]
  exact congrArg (Abelian.CechCoordinates.abelianCechCoordinates ((Rational.BettiSheafComparison.rationalAbelianSingularResolution X).X 1).obj U 1).symm
    d.sheafified_horizontal_d

theorem Singular.CechDescent.SingularCechDescentData.native_vertical_d :
    ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex U (Rational.BettiSheafComparison.rationalAbelianSingularResolution X)).d 1 2).f 0 d.nativeVertical =
      FlasqueCechD.abelianCechHorizontalAugmentation U (Rational.BettiSheafComparison.rationalAbelianSingularResolution X) 2
        ((Singular.GammaAugmentation.rationalSingularToGamma X).f 2 c.val) := by
  change ((CategoryTheory.cechComplexFunctor U).map
      ((Rational.BettiSheafComparison.rationalAbelianSingularResolution X).d 1 2).hom).f 0
        ((Abelian.CechCoordinates.abelianCechCoordinates ((Rational.BettiSheafComparison.rationalAbelianSingularResolution X).X 1).obj U 0).symm
          (Singular.CechSheafification.singularCechSheafify U 1 0 d.vertical)) = _
  rw [Cech.IntrinsicOperators.abelianCechCoordinates_symm_coefficient, d.sheafified_vertical_d]
  apply (Abelian.CechCoordinates.abelianCechCoordinates ((Rational.BettiSheafComparison.rationalAbelianSingularResolution X).X 2).obj U 0).injective
  rw [AddEquiv.apply_symm_apply]
  exact (Singular.GammaAugmentation.rationalSingularToGamma_augmentation X U 2 c.val).symm

theorem Intrinsic.SingularBoundary.singularCechSheafify_neg (q p : ℕ)
    (k : Rational.Cech.RationalCech.CechCochain ((AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X).X q) U p) :
    Singular.CechSheafification.singularCechSheafify U q p (-k) = -Singular.CechSheafification.singularCechSheafify U q p k := by
  funext a
  exact map_neg ((Singular.CechSheafification.rationalSingularSheafUnit (X := X) q).app (Opposite.op (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a))).hom
    (k a)

theorem Singular.CechDescent.SingularCechDescentData.native_horizontal_delta
    (k : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (Rational.Cech.RationalCech.cechComplex (Cech.Obj.RationalCech.locallyConstantPresheaf X) U) 2)
    (hk : Cech.Obj.RationalCech.locallyConstantCechEvaluation X U 2 k.val =
      -Rational.Cech.RationalCech.cechDelta ((AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X).X 0) U 1 d.horizontal) :
    ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex U (Rational.BettiSheafComparison.rationalAbelianSingularResolution X)).X 0).d 1 2 d.nativeHorizontal =
      -((CategoryTheory.cechComplexFunctor U).map (Abelian.SingularAugmentation.rationalAbelianConstantAugmentation X).hom).f 2
        ((Abelian.CechCoordinates.abelianCechCoordinates (Rational.HolomorphicPeriod.rationalConstantAbelianSheaf X).obj U 2).symm k.val) := by
  change ((CategoryTheory.cechComplexFunctor U).obj ((Rational.BettiSheafComparison.rationalAbelianSingularResolution X).X 0).obj).d 1 2
      ((Abelian.CechCoordinates.abelianCechCoordinates ((Rational.BettiSheafComparison.rationalAbelianSingularResolution X).X 0).obj U 1).symm
        (Singular.CechSheafification.singularCechSheafify U 0 1 d.horizontal)) = _
  rw [Cech.IntrinsicOperators.abelianCechCoordinates_symm_d, Cech.IntrinsicOperators.abelianCechCoordinates_symm_coefficient, ← map_neg]
  congr 1
  rw [Abelian.SingularAugmentation.rationalAbelianConstantAugmentation_cech, hk, Intrinsic.SingularBoundary.singularCechSheafify_neg,
    neg_neg, Singular.CechSheafification.singularCechSheafify_delta]

end

/-! The signed native total boundary comparing descended Cech and original singular classes. -/

open _root_.CategoryTheory _root_.TopologicalSpace _root_.TopCat.Sheaf

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}} {I : Type} {U : I → Opens X}
  {c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of ℚ ℚ) X 2} (d : Singular.CechDescent.SingularCechDescentData c U)

def Singular.CechDescent.SingularCechDescentData.nativeTotalPrimitive :
    ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex U (Rational.BettiSheafComparison.rationalAbelianSingularResolution X)).total (.up ℕ)).X 1 :=
  -(SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex U (Rational.BettiSheafComparison.rationalAbelianSingularResolution X)).ιTotal (.up ℕ) 0 1 1 rfl
      d.nativeHorizontal -
    (SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex U (Rational.BettiSheafComparison.rationalAbelianSingularResolution X)).ιTotal (.up ℕ) 1 0 1 rfl d.nativeVertical

theorem Singular.CechDescent.SingularCechDescentData.nativeTotalPrimitive_d
    (k : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (Rational.Cech.RationalCech.cechComplex (Cech.Obj.RationalCech.locallyConstantPresheaf X) U) 2)
    (hk : Cech.Obj.RationalCech.locallyConstantCechEvaluation X U 2 k.val =
      -Rational.Cech.RationalCech.cechDelta ((AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X).X 0) U 1 d.horizontal) :
    ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex U (Rational.BettiSheafComparison.rationalAbelianSingularResolution X)).total (.up ℕ)).d 1 2
        d.nativeTotalPrimitive =
      (FlasqueCechD.abelianCechVerticalEdge U (Abelian.SingularAugmentation.rationalAbelianConstantAugmentation X)
        (Abelian.SingularAugmentation.rationalAbelianConstantAugmentation_d X)).f 2
          ((Abelian.CechCoordinates.abelianCechCoordinates (Rational.HolomorphicPeriod.rationalConstantAbelianSheaf X).obj U 2).symm k.val) -
        (FlasqueCechD.abelianCechHorizontalEdge U (Rational.BettiSheafComparison.rationalAbelianSingularResolution X)).f 2
          ((Singular.GammaAugmentation.rationalSingularToGamma X).f 2 c.val) := by
  let B := SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex U (Rational.BettiSheafComparison.rationalAbelianSingularResolution X)
  have hh : (B.total (.up ℕ)).d 1 2 (B.ιTotal (.up ℕ) 0 1 1 rfl d.nativeHorizontal) =
      B.ιTotal (.up ℕ) 1 1 2 rfl ((B.d 0 1).f 1 d.nativeHorizontal) +
        B.ιTotal (.up ℕ) 0 2 2 rfl ((B.X 0).d 1 2 d.nativeHorizontal) := by
    simpa only [pow_zero, one_smul, AddCommGrpCat.hom_add_apply, ConcreteCategory.comp_apply] using
      (ConcreteCategory.congr_hom ((SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.ιTotal_d_upNat B) 0 1) d.nativeHorizontal)
  have hv : (B.total (.up ℕ)).d 1 2 (B.ιTotal (.up ℕ) 1 0 1 rfl d.nativeVertical) =
      B.ιTotal (.up ℕ) 2 0 2 rfl ((B.d 1 2).f 0 d.nativeVertical) +
        -B.ιTotal (.up ℕ) 1 1 2 rfl ((B.X 1).d 0 1 d.nativeVertical) := by
    simpa [ConcreteCategory.comp_apply, Units.smul_def] using
      (ConcreteCategory.congr_hom ((SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.ιTotal_d_upNat B) 1 0) d.nativeVertical)
  rw [d.native_middle, d.native_horizontal_delta k hk, map_neg] at hh
  rw [d.native_vertical_d] at hv
  rw [FlasqueCechD.abelianCechVerticalEdge_f, FlasqueCechD.abelianCechHorizontalEdge_f]
  change (B.total (.up ℕ)).d 1 2
      (-B.ιTotal (.up ℕ) 0 1 1 rfl d.nativeHorizontal -
        B.ιTotal (.up ℕ) 1 0 1 rfl d.nativeVertical) =
    B.ιTotal (.up ℕ) 0 2 2 rfl
      (((CategoryTheory.cechComplexFunctor U).map (Abelian.SingularAugmentation.rationalAbelianConstantAugmentation X).hom).f 2
        ((Abelian.CechCoordinates.abelianCechCoordinates (Rational.HolomorphicPeriod.rationalConstantAbelianSheaf X).obj U 2).symm k.val)) -
      B.ιTotal (.up ℕ) 2 0 2 rfl
        (FlasqueCechD.abelianCechHorizontalAugmentation U (Rational.BettiSheafComparison.rationalAbelianSingularResolution X) 2
          ((Singular.GammaAugmentation.rationalSingularToGamma X).f 2 c.val))
  rw [map_sub, map_neg, hh, hv]
  exact (show ∀ a b m : (B.total (.up ℕ)).X 2,
    -(m + -a) - (b + -m) = a - b from by intros; abel) _ _ _

end

end OAI.AlgebraicGeometry.DivisorClass.Chern

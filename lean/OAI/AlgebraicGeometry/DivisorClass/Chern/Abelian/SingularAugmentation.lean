import OAI.AlgebraicGeometry.DivisorClass.Chern.Singular.CechSheafification
import OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.SheafAugmentation

/-! # Singular Augmentation -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Abelian.SingularAugmentation

noncomputable section

/-! The native degree-zero singular augmentation is the original locally constant point evaluation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.SheafAugmentation.RationalCech

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (X : TopCat.{0})

def rationalAbelianConstantAugmentation :
    Rational.HolomorphicPeriod.rationalConstantAbelianSheaf X ⟶ (Rational.BettiSheafComparison.rationalAbelianSingularResolution X).X 0 :=
  (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalSheafForget X).map (Rational.SheafAugmentation.RationalCech.locallyConstantRationalSheafAugmentation X)

theorem rationalAbelianConstantAugmentation_zeroIso [LocallyPathConnectedSpace X] :
    (Rational.BettiSheafComparison.rationalConstantAbelianZeroIso X).hom ≫
        (HodgeConjecture.DegreeTwo.ThomGoodShiftFlasque.Constructions.cochainZeroHomologyAugmentation (Rational.BettiSheafComparison.rationalAbelianSingularResolution X)).f 0 =
      rationalAbelianConstantAugmentation X := by
  let K := HodgeConjecture.DegreeTwo.SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex X
  let G := AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalSheafForget X
  have hc := ThomSourceOrientation.cochainLeftExactZeroHomologyIso_inclusion K G
  rw [ThomSourceOrientation.cochainLeftExactZeroHomologyIso_hom_eq, AlgebraicTopology.Cohomology.Singular.LeftExactHomologyIso.leftExactHomologyComparison_eq_mapHomologyIso',
    ShortComplex.mapHomologyIso'_eq_mapHomologyIso] at hc
  have hi : (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalSheafForgetHomologyIso K 0).inv ≫
      (Rational.BettiSheafComparison.rationalAbelianSingularResolution X).isoHomologyπ₀.inv ≫
        (Rational.BettiSheafComparison.rationalAbelianSingularResolution X).iCycles 0 =
      G.map (K.isoHomologyπ₀.inv ≫ K.iCycles 0) :=
    ((K.sc 0).mapHomologyIso G).inv_comp_eq.mpr hc.symm
  rw [HodgeConjecture.DegreeTwo.ThomGoodShiftFlasque.Constructions.cochainZeroHomologyAugmentation_f_zero]
  unfold Rational.BettiSheafComparison.rationalConstantAbelianZeroIso
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
  rw [hi, ← Functor.map_comp]
  exact congrArg G.map (ThomSourceOrientation.RationalCech.locallyConstantRationalSheafZeroIso_inclusion X)

theorem rationalAbelianConstantAugmentation_d :
    rationalAbelianConstantAugmentation X ≫ (Rational.BettiSheafComparison.rationalAbelianSingularResolution X).d 0 1 = 0 := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro k
  change (AlgebraicTopology.Cohomology.Singular.OpenSheafComparison.singularSheafSections (ModuleCat.of ℚ ℚ) X U.unop).d 0 1
    ((Rational.SheafAugmentation.RationalCech.locallyConstantRationalSheafAugmentation X).hom.app U k) = 0
  rw [Rational.SheafAugmentation.RationalCech.locallyConstantRationalSheafAugmentation_hom]
  have h := ConcreteCategory.congr_hom
    ((AlgebraicTopology.Cohomology.Singular.OpenSheafComparison.singularCochainsToOpenSheafSections (ModuleCat.of ℚ ℚ) X U.unop).comm 0 1)
    (AlgebraicTopology.Cohomology.Singular.Augmentation.locallyConstantToSingularZero (ModuleCat.of ℚ ℚ) (TopCat.of U.unop) k)
  have hz := ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.Augmentation.locallyConstantToSingularZero_d (ModuleCat.of ℚ ℚ) (TopCat.of U.unop)) k
  change (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) (TopCat.of U.unop)).d 0 1
    (AlgebraicTopology.Cohomology.Singular.Augmentation.locallyConstantToSingularZero (ModuleCat.of ℚ ℚ) (TopCat.of U.unop) k) = 0 at hz
  change (AlgebraicTopology.Cohomology.Singular.OpenSheafComparison.singularSheafSections (ModuleCat.of ℚ ℚ) X U.unop).d 0 1
      ((AlgebraicTopology.Cohomology.Singular.OpenSheafComparison.singularCochainsToOpenSheafSections (ModuleCat.of ℚ ℚ) X U.unop).f 0
        (AlgebraicTopology.Cohomology.Singular.Augmentation.locallyConstantToSingularZero (ModuleCat.of ℚ ℚ) (TopCat.of U.unop) k)) =
    (AlgebraicTopology.Cohomology.Singular.OpenSheafComparison.singularCochainsToOpenSheafSections (ModuleCat.of ℚ ℚ) X U.unop).f 1
      ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) (TopCat.of U.unop)).d 0 1
        (AlgebraicTopology.Cohomology.Singular.Augmentation.locallyConstantToSingularZero (ModuleCat.of ℚ ℚ) (TopCat.of U.unop) k)) at h
  rw [hz, map_zero] at h
  exact h

theorem rationalAbelianConstantAugmentation_cech {I : Type} (U : I → Opens X) (p : ℕ)
    (k : Rational.Cech.RationalCech.CechCochain (Cech.Obj.RationalCech.locallyConstantPresheaf X) U p) :
    CechClasses.abelianCechCoefficient U (rationalAbelianConstantAugmentation X).hom p k =
      Singular.CechSheafification.singularCechSheafify U 0 p (Cech.Obj.RationalCech.locallyConstantCechEvaluation X U p k) := by
  funext a
  change (Rational.SheafAugmentation.RationalCech.locallyConstantRationalSheafAugmentation X).hom.app (Opposite.op (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a))
    (k a) = _
  rw [Rational.SheafAugmentation.RationalCech.locallyConstantRationalSheafAugmentation_hom]
  rfl

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Abelian.SingularAugmentation

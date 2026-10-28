import OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.ComplexSheafMap
import OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.ComplexEvaluation
import OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.ComplexPeriod
import OAI.AlgebraicGeometry.DivisorClass.Chern.Abelian.SingularAugmentation

/-! # Complex Augmentation -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.ComplexAugmentation

noncomputable section

/-! Coefficient change preserves the original locally constant singular augmentation. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem rationalToComplexCochainMap_locallyConstant (X : TopCat.{0}) (q : LocallyConstant X ℚ) :
    (ComplexCochains.rationalToComplexCochainMap X).f 0 (AlgebraicTopology.Cohomology.Singular.Augmentation.locallyConstantToSingularZero (ModuleCat.of ℚ ℚ) X q) =
      AlgebraicTopology.Cohomology.Singular.Augmentation.locallyConstantToSingularZero (ModuleCat.of ℂ ℂ) X
        ⟨fun x => (q x : ℂ), q.isLocallyConstant.comp (fun a : ℚ => (a : ℂ))⟩ := by
  apply (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj X) (ModuleCat.of ℂ ℂ) 0).toLinearEquiv.injective
  funext s
  change (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj X) (ModuleCat.of ℂ ℂ) 0).hom
      ((ComplexCochains.rationalToComplexCochainMap X).f 0 (AlgebraicTopology.Cohomology.Singular.Augmentation.locallyConstantToSingularZero (ModuleCat.of ℚ ℚ) X q)) s =
    (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj X) (ModuleCat.of ℂ ℂ) 0).hom
      (AlgebraicTopology.Cohomology.Singular.Augmentation.locallyConstantToSingularZero (ModuleCat.of ℂ ℂ) X
        ⟨fun x => (q x : ℂ), q.isLocallyConstant.comp (fun a : ℚ => (a : ℂ))⟩) s
  rw [AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso_hom_apply, AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso_hom_apply, ComplexEvaluation.rationalToComplexCochainMap_apply]
  have hev (R : Type) [Ring R] (A : ModuleCat.{0} R) (f : LocallyConstant X A) :
      AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation (TopCat.toSSet.obj X) A s (AlgebraicTopology.Cohomology.Singular.Augmentation.locallyConstantToSingularZero A X f) =
        f (TopCat.toSSetObj₀Equiv s) :=
    (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso_hom_apply (TopCat.toSSet.obj X) A (AlgebraicTopology.Cohomology.Singular.Augmentation.locallyConstantToSingularZero A X f) s).symm.trans
      ((AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso_apply_simplex A X (AlgebraicTopology.Cohomology.Singular.Augmentation.locallyConstantToSingularZero A X f) s).symm.trans
        (AlgebraicTopology.Cohomology.Singular.Augmentation.locallyConstantToSingularZero_apply A X f (TopCat.toSSetObj₀Equiv s)))
  exact (congrArg (fun a : ℚ => (a : ℂ)) (hev ℚ (ModuleCat.of ℚ ℚ) q)).trans
    (hev ℂ (ModuleCat.of ℂ ℂ) ⟨fun x => (q x : ℂ), q.isLocallyConstant.comp (fun a : ℚ => (a : ℂ))⟩).symm

theorem rationalComplexPresheafMap_augmentation (X : TopCat.{0}) :
    Functor.whiskerRight (Cech.Obj.RationalCech.locallyConstantSingularAugmentation X) AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForget ≫
        (ComplexPresheaf.rationalComplexPresheafMap X).f 0 =
      (ComplexPeriod.rationalConstantComplexSheafMap X).hom ≫
        Functor.whiskerRight (AlgebraicTopology.Cohomology.Singular.Augmentation.Comparison.locallyConstantSingularAugmentation X) Complex.SheafForget.complexModuleForget := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro q
  exact rationalToComplexCochainMap_locallyConstant (TopCat.of U.unop) q

def complexAbelianConstantAugmentation (X : TopCat.{0}) :
    Abelian.ManifoldDeRham.abelianLocallyConstantComplexSheaf X ⟶ (ComplexSheafMap.complexAbelianSingularResolution X).X 0 :=
  (Complex.SheafForget.complexSheafForget X).map (AlgebraicTopology.Cohomology.Singular.SheafResolution.locallyConstantSingularSheafAugmentation X)

theorem rationalComplexSingularSheafMap_augmentation (X : TopCat.{0}) :
    Abelian.SingularAugmentation.rationalAbelianConstantAugmentation X ≫ (ComplexSheafMap.rationalComplexSingularSheafMap X).f 0 =
      ComplexPeriod.rationalConstantComplexSheafMap X ≫ complexAbelianConstantAugmentation X := by
  apply ObjectProperty.hom_ext
  have hQ := congrArg (fun f => Functor.whiskerRight f AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForget)
    (SheafAugmentation.RationalCech.locallyConstantRationalSheafAugmentation_hom X)
  have hC := congrArg (fun f => Functor.whiskerRight f Complex.SheafForget.complexModuleForget)
    (AlgebraicTopology.Cohomology.Singular.SheafResolution.locallyConstantSingularSheafAugmentation_hom X)
  change (Abelian.SingularAugmentation.rationalAbelianConstantAugmentation X).hom ≫ ((ComplexSheafMap.rationalComplexSingularSheafMap X).f 0).hom =
    (ComplexPeriod.rationalConstantComplexSheafMap X).hom ≫ (complexAbelianConstantAugmentation X).hom
  rw [show (Abelian.SingularAugmentation.rationalAbelianConstantAugmentation X).hom =
      Functor.whiskerRight (Cech.Obj.RationalCech.locallyConstantSingularAugmentation X) AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForget ≫
        Functor.whiskerRight (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
          ((AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X).X 0)) AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForget from hQ]
  rw [Category.assoc, ComplexSheafMap.rationalComplexSingularSheafMap_unit, ← Category.assoc,
    rationalComplexPresheafMap_augmentation, Category.assoc]
  exact congrArg (fun f => (ComplexPeriod.rationalConstantComplexSheafMap X).hom ≫ f) hC.symm

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.ComplexAugmentation

import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ModuleForgetCocycleClasses
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntegerSheafAugmentation
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntegralSheafCoefficients
import OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.ComplexSheafMap
import OAI.AlgebraicGeometry.DivisorClass.Chern.Abelian.SingularAugmentation

/-! # Rational Integer Sheaf Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RationalIntegerSheafComparison

noncomputable section

/-! Scalar restriction on the original rational singular sheaf
resolution, including its point-function augmentation and global sections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

variable (X : TopCat.{0})

def rationalIntegerSingularSheafIso :
    DivisorClass.Chern.Rational.BettiSheafComparison.rationalAbelianSingularResolution X ≅
      IntegerSingularSheafComparison.integerAbelianSingularResolution (ModuleCat.of ℤ ℚ) X :=
  (DivisorClass.Chern.ModuleSheafificationForget.moduleForgetSheafificationComplexIso ℚ X
      (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X)).symm ≪≫
    ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).mapHomologicalComplex
      (.up ℕ)).mapIso (ModuleForgetCocycleClasses.rationalIntegerPresheafIso X) ≪≫
    DivisorClass.Chern.ModuleSheafificationForget.moduleForgetSheafificationComplexIso ℤ X (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℤ ℚ) X)

theorem rationalIntegerSingularSheafIso_unit (n : ℕ) :
    Functor.whiskerRight (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
        ((AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X).X n)) AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForget ≫
      ((rationalIntegerSingularSheafIso X).hom.f n).hom =
    (ModuleForgetCocycleClasses.rationalIntegerPresheafIso X).hom.f n ≫
      Functor.whiskerRight (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
        ((AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℤ ℚ) X).X n)) IntegerSingularSheafComparison.integerModuleForget := by
  let J := Opens.grothendieckTopology X
  let Q : X.Presheaf (ModuleCat.{0} ℚ) := (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X).X n
  let Z : X.Presheaf (ModuleCat.{0} ℤ) := (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℤ ℚ) X).X n
  let CQ : X.Presheaf AddCommGrpCat.{0} := Q ⋙ AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForget
  let CZ : X.Presheaf AddCommGrpCat.{0} := Z ⋙ IntegerSingularSheafComparison.integerModuleForget
  let Q0 : X.Presheaf AddCommGrpCat.{0} := CategoryTheory.sheafify J Q ⋙ AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForget
  let Q1 : X.Presheaf AddCommGrpCat.{0} := CategoryTheory.sheafify J CQ
  let Z1 : X.Presheaf AddCommGrpCat.{0} := CategoryTheory.sheafify J CZ
  let Z0 : X.Presheaf AddCommGrpCat.{0} := CategoryTheory.sheafify J Z ⋙ IntegerSingularSheafComparison.integerModuleForget
  let f : CQ ⟶ CZ := (ModuleForgetCocycleClasses.rationalIntegerPresheafIso X).hom.f n
  let uQ : CQ ⟶ Q0 := Functor.whiskerRight (CategoryTheory.toSheafify J Q) AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForget
  let uZ : CZ ⟶ Z0 := Functor.whiskerRight (CategoryTheory.toSheafify J Z) IntegerSingularSheafComparison.integerModuleForget
  let eQ : CQ ⟶ Q1 := CategoryTheory.toSheafify J CQ
  let eZ : CZ ⟶ Z1 := CategoryTheory.toSheafify J CZ
  let a : Q0 ⟶ Q1 := (DivisorClass.Chern.ModuleSheafificationForget.moduleForgetSheafificationIso ℚ X Q).inv.hom
  let b : Q1 ⟶ Z1 := CategoryTheory.sheafifyMap J f
  let c : Z1 ⟶ Z0 := (DivisorClass.Chern.ModuleSheafificationForget.moduleForgetSheafificationIso ℤ X Z).hom.hom
  have h1 : uQ ≫ a = eQ := DivisorClass.Chern.Rational.ComplexSheafMap.moduleForgetSheafificationIso_inv_unit X ℚ Q
  have h2 : eQ ≫ b = f ≫ eZ := (CategoryTheory.toSheafify_naturality J f).symm
  have h3 : eZ ≫ c = uZ := DivisorClass.Chern.ModuleSheafificationForget.moduleForgetSheafificationIso_unit ℤ X Z
  have hh : uQ ≫ (a ≫ b ≫ c) = f ≫ uZ :=
    (Category.assoc uQ a (b ≫ c)).symm.trans
      ((congrArg (fun v : CQ ⟶ Q1 => v ≫ b ≫ c) h1).trans
        ((Category.assoc eQ b c).symm.trans
          ((congrArg (fun v : CQ ⟶ Z1 => v ≫ c) h2).trans
            ((Category.assoc f eZ c).trans
              (congrArg (fun v : CZ ⟶ Z0 => f ≫ v) h3)))))
  exact hh

theorem rationalIntegerPresheafIso_augmentation :
    Functor.whiskerRight (DivisorClass.Chern.Cech.Obj.RationalCech.locallyConstantSingularAugmentation X) AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForget ≫
      (ModuleForgetCocycleClasses.rationalIntegerPresheafIso X).hom.f 0 =
    (IntegralSheafCoefficients.originalRationalConstantIso X).inv.hom ≫
      Functor.whiskerRight (LocallyConstantModuleSheaf.coefficientLocallyConstantAugmentation (ModuleCat.of ℤ ℚ) X)
        IntegerSingularSheafComparison.integerModuleForget := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro q
  exact ModuleForgetCocycleClasses.rationalIntegerAbelianCochainIso_locallyConstant (TopCat.of U.unop) q

theorem rationalIntegerSingularSheafIso_augmentation :
    DivisorClass.Chern.Abelian.SingularAugmentation.rationalAbelianConstantAugmentation X ≫ (rationalIntegerSingularSheafIso X).hom.f 0 =
      (IntegralSheafCoefficients.originalRationalConstantIso X).inv ≫
        IntegerSheafAugmentation.integerAbelianConstantAugmentation X (ModuleCat.of ℤ ℚ) := by
  let LQ : X.Presheaf AddCommGrpCat.{0} := (DivisorClass.Chern.Rational.HolomorphicPeriod.rationalConstantAbelianSheaf X).obj
  let LZ : X.Presheaf AddCommGrpCat.{0} :=
    (IntegerSingularSheafComparison.integerLocallyConstantAbelianSheaf (ModuleCat.of ℤ ℚ) X).obj
  let CQ : X.Presheaf AddCommGrpCat.{0} :=
    (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X).X 0 ⋙ AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForget
  let CZ : X.Presheaf AddCommGrpCat.{0} :=
    (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℤ ℚ) X).X 0 ⋙ IntegerSingularSheafComparison.integerModuleForget
  let SQ : X.Presheaf AddCommGrpCat.{0} := ((DivisorClass.Chern.Rational.BettiSheafComparison.rationalAbelianSingularResolution X).X 0).obj
  let SZ : X.Presheaf AddCommGrpCat.{0} :=
    ((IntegerSingularSheafComparison.integerAbelianSingularResolution (ModuleCat.of ℤ ℚ) X).X 0).obj
  let aQ : LQ ⟶ CQ :=
    Functor.whiskerRight (DivisorClass.Chern.Cech.Obj.RationalCech.locallyConstantSingularAugmentation X) AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForget
  let aZ : LZ ⟶ CZ :=
    Functor.whiskerRight (LocallyConstantModuleSheaf.coefficientLocallyConstantAugmentation (ModuleCat.of ℤ ℚ) X) IntegerSingularSheafComparison.integerModuleForget
  let uQ : CQ ⟶ SQ :=
    Functor.whiskerRight (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
      ((AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X).X 0)) AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForget
  let uZ : CZ ⟶ SZ :=
    Functor.whiskerRight (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
      ((AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℤ ℚ) X).X 0)) IntegerSingularSheafComparison.integerModuleForget
  let iso : SQ ⟶ SZ := ((rationalIntegerSingularSheafIso X).hom.f 0).hom
  let f : CQ ⟶ CZ := (ModuleForgetCocycleClasses.rationalIntegerPresheafIso X).hom.f 0
  let a : LQ ⟶ LZ := (IntegralSheafCoefficients.originalRationalConstantIso X).inv.hom
  let bQ : LQ ⟶ SQ := (DivisorClass.Chern.Abelian.SingularAugmentation.rationalAbelianConstantAugmentation X).hom
  let bZ : LZ ⟶ SZ := (IntegerSheafAugmentation.integerAbelianConstantAugmentation X (ModuleCat.of ℤ ℚ)).hom
  have hQraw := congrArg (fun v => Functor.whiskerRight v AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForget)
    (DivisorClass.Chern.Rational.SheafAugmentation.RationalCech.locallyConstantRationalSheafAugmentation_hom X)
  have hZraw := congrArg (fun v => Functor.whiskerRight v IntegerSingularSheafComparison.integerModuleForget)
    (IntegerSheafAugmentation.coefficientSingularSheafAugmentation_hom (ModuleCat.of ℤ ℚ) X)
  have hQ : bQ = aQ ≫ uQ := hQraw
  have hZ : bZ = aZ ≫ uZ := hZraw
  have hunit : uQ ≫ iso = f ≫ uZ := rationalIntegerSingularSheafIso_unit X 0
  have haug : aQ ≫ f = a ≫ aZ := rationalIntegerPresheafIso_augmentation X
  have hh : bQ ≫ iso = a ≫ bZ :=
    (congrArg (fun v : LQ ⟶ SQ => v ≫ iso) hQ).trans
      ((Category.assoc aQ uQ iso).trans
        ((congrArg (fun v : CQ ⟶ SZ => aQ ≫ v) hunit).trans
          ((Category.assoc aQ f uZ).symm.trans
            ((congrArg (fun v : LQ ⟶ CZ => v ≫ uZ) haug).trans
              ((Category.assoc a aZ uZ).trans
                (congrArg (fun v : LZ ⟶ SZ => a ≫ v) hZ.symm))))))
  apply Sheaf.hom_ext
  exact hh

theorem rationalIntegerSingularSheafIso_zero [LocallyPathConnectedSpace X] :
    (DivisorClass.Chern.Rational.BettiSheafComparison.rationalConstantAbelianZeroIso X).hom ≫
      HomologicalComplex.homologyMap (rationalIntegerSingularSheafIso X).hom 0 =
    (IntegralSheafCoefficients.originalRationalConstantIso X).inv ≫
      (IntegerSingularSheafComparison.integerConstantAbelianZeroIso (ModuleCat.of ℤ ℚ) X).hom :=
  DivisorClass.Chern.Intrinsic.AugmentationNaturality.cochainAugmentationZeroIso_naturality _ _ _ _ _ _
    (DivisorClass.Chern.Abelian.SingularAugmentation.rationalAbelianConstantAugmentation_zeroIso X)
    (IntegerSheafAugmentation.integerAbelianConstantAugmentation_zeroIso X (ModuleCat.of ℤ ℚ))
    (rationalIntegerSingularSheafIso_augmentation X)

theorem rationalIntegerSingularSheafIso_globalSections :
    DivisorClass.Chern.ModuleGlobalSectionsForget.moduleSingularToAbelianSections ℚ X (ModuleCat.of ℚ ℚ) ≫
        ((CycleClass.Geometric.FlasqueLowDegree.Cycles.sheafGlobalSections X).mapHomologicalComplex (.up ℕ)).map
          (rationalIntegerSingularSheafIso X).hom =
      (ModuleForgetCocycleClasses.rationalIntegerAbelianCochainIso X).hom ≫
        DivisorClass.Chern.ModuleGlobalSectionsForget.moduleSingularToAbelianSections ℤ X (ModuleCat.of ℤ ℚ) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro c
  let incl := Opens.inclusion' (⊤ : Opens X)
  let qtop := (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ) incl).f n c
  let etaZ := CategoryTheory.toSheafify (Opens.grothendieckTopology X)
    ((AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℤ ℚ) X).X n)
  have hu := ConcreteCategory.congr_hom (C := AddCommGrpCat.{0})
    (congrArg (fun f => f.app (op (⊤ : Opens X))) (rationalIntegerSingularSheafIso_unit X n)) qtop
  have hn := ConcreteCategory.congr_hom
    (congrArg (fun f => f.f n) (ModuleForgetCocycleClasses.rationalIntegerAbelianCochainIso_naturality incl)) c
  change (ModuleForgetCocycleClasses.rationalIntegerAbelianCochainIso (TopCat.of (⊤ : Opens X))).hom.f n qtop =
    (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℤ ℚ) incl).f n
      ((ModuleForgetCocycleClasses.rationalIntegerAbelianCochainIso X).hom.f n c) at hn
  change (((rationalIntegerSingularSheafIso X).hom.f n).hom.app (op (⊤ : Opens X)))
      ((AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.singularCochainsToSheafSections (ModuleCat.of ℚ ℚ) X).f n c) =
    etaZ.app (op (⊤ : Opens X))
      ((ModuleForgetCocycleClasses.rationalIntegerAbelianCochainIso (TopCat.of (⊤ : Opens X))).hom.f n qtop) at hu
  exact hu.trans (congrArg (fun v => etaZ.app (op (⊤ : Opens X)) v) hn)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RationalIntegerSheafComparison

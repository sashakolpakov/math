import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RationalIntegerSheafComparison
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CoefficientComparisonDiagrams
import OAI.AlgebraicGeometry.DivisorClass.Chern.Intrinsic.BettiSheafMaps

/-! # Rational Integer Betti Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RationalIntegerBettiComparison

noncomputable section

/-! The scalar-restriction comparison commutes with the original ChernClass
Betti-to-sheaf isomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

open OAI.AlgebraicGeometry.DivisorClass.Chern.Intrinsic.BettiSheafMaps

variable (X : TopCat.{0}) [MetrizableSpace X] [StronglyLocallyContractibleSpace X]
  [LocallyPathConnectedSpace X]

omit [MetrizableSpace X] in
theorem integerSingularBettiSheafMap_hom_sections (M : ModuleCat.{0} ℤ) (n : ℕ) :
    IntegerSingularSheafComparison.integerSingularBettiSheafMap M X n =
      (((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X).sc (n + 1)).mapHomologyIso IntegerSingularSheafComparison.integerModuleForget).inv ≫
        HomologicalComplex.homologyMap (DivisorClass.Chern.ModuleGlobalSectionsForget.moduleSingularToAbelianSections ℤ X M) (n + 1) ≫
          DivisorClass.Chern.Intrinsic.AugmentationNaturality.nativeSectionCohomologyMapOfZero (IntegerSingularSheafComparison.integerAbelianSingularResolution M X)
            (IntegerSingularSheafComparison.integerAbelianSingularResolution_exact M X) (IntegerSingularSheafComparison.integerConstantAbelianZeroIso M X) n := by
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{0} (.up ℕ) (n + 1)
  let FC := IntegerSingularSheafComparison.integerModuleForget.mapHomologicalComplex (.up ℕ)
  let K := AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X
  let L := AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.singularSheafGlobalSections M X
  let R := CycleClass.Geometric.FlasqueLowDegree.Cycles.sheafGlobalSectionsComplex (IntegerSingularSheafComparison.integerAbelianSingularResolution M X)
  let A : AddCommGrpCat.{0} := IntegerSingularSheafComparison.integerModuleForget.obj (K.homology (n + 1))
  let B : AddCommGrpCat.{0} := IntegerSingularSheafComparison.integerModuleForget.obj (L.homology (n + 1))
  let C : AddCommGrpCat.{0} := H.obj (FC.obj K)
  let D : AddCommGrpCat.{0} := H.obj (FC.obj L)
  let S : AddCommGrpCat.{0} := H.obj R
  let T : AddCommGrpCat.{0} :=
    (Sheaf.functorH (Opens.grothendieckTopology X) (n + 1)).obj
      (IntegerSingularSheafComparison.integerLocallyConstantAbelianSheaf M X)
  let m : A ⟶ B := IntegerSingularSheafComparison.integerModuleForget.map
    (HomologicalComplex.homologyMap (AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.singularCochainsToSheafSections M X) (n + 1))
  let a : A ⟶ C := ((K.sc (n + 1)).mapHomologyIso IntegerSingularSheafComparison.integerModuleForget).inv
  let b : B ⟶ D := ((L.sc (n + 1)).mapHomologyIso IntegerSingularSheafComparison.integerModuleForget).inv
  let c : C ⟶ D := H.map (FC.map (AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.singularCochainsToSheafSections M X))
  let d : D ⟶ S := H.map (IntegerSingularSheafComparison.integerSingularSectionsForgetIso M X).hom
  let p : C ⟶ S := H.map (DivisorClass.Chern.ModuleGlobalSectionsForget.moduleSingularToAbelianSections ℤ X M)
  let e : S ⟶ T := DivisorClass.Chern.Intrinsic.AugmentationNaturality.nativeSectionCohomologyMapOfZero (IntegerSingularSheafComparison.integerAbelianSingularResolution M X)
    (IntegerSingularSheafComparison.integerAbelianSingularResolution_exact M X) (IntegerSingularSheafComparison.integerConstantAbelianZeroIso M X) n
  have hn : m ≫ b = a ≫ c := ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor _ _ (n + 1)).map
      (AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.singularCochainsToSheafSections M X)) IntegerSingularSheafComparison.integerModuleForget
  have hs : DivisorClass.Chern.ModuleGlobalSectionsForget.moduleSingularToAbelianSections ℤ X M =
      FC.map (AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.singularCochainsToSheafSections M X) ≫ (IntegerSingularSheafComparison.integerSingularSectionsForgetIso M X).hom := rfl
  have hp : p = c ≫ d := (congrArg H.map hs).trans (H.map_comp _ _)
  have h0 : m ≫ (b ≫ d) = a ≫ p :=
    (Category.assoc m b d).symm.trans
      ((congrArg (fun v : A ⟶ D => v ≫ d) hn).trans
        ((Category.assoc a c d).trans (congrArg (fun v : C ⟶ S => a ≫ v) hp.symm)))
  have hh : m ≫ (b ≫ d) ≫ e = a ≫ p ≫ e :=
    (Category.assoc m (b ≫ d) e).symm.trans
      ((congrArg (fun v : A ⟶ S => v ≫ e) h0).trans (Category.assoc a p e))
  exact hh

theorem rationalIntegerCohomologyIso_betti (n : ℕ) :
    (ModuleForgetCocycleClasses.rationalIntegerCohomologyIso X (n + 1)).hom ≫
        IntegerSingularSheafComparison.integerSingularBettiSheafMap (ModuleCat.of ℤ ℚ) X n =
      (DivisorClass.Chern.Rational.BettiCechSheafComparison.rationalBettiCechSheafIso X n).hom ≫
        (Sheaf.functorH (Opens.grothendieckTopology X) (n + 1)).map
          (IntegralSheafCoefficients.originalRationalConstantIso X).inv := by
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{0} (.up ℕ) (n + 1)
  let Q := AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X
  let Z := AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℤ ℚ) X
  let A : AddCommGrpCat.{0} := AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForget.obj (Q.homology (n + 1))
  let B : AddCommGrpCat.{0} := H.obj ((AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForget.mapHomologicalComplex (.up ℕ)).obj Q)
  let C : AddCommGrpCat.{0} := H.obj ((IntegerSingularSheafComparison.integerModuleForget.mapHomologicalComplex (.up ℕ)).obj Z)
  let D : AddCommGrpCat.{0} := IntegerSingularSheafComparison.integerModuleForget.obj (Z.homology (n + 1))
  let R : AddCommGrpCat.{0} := H.obj (CycleClass.Geometric.FlasqueLowDegree.Cycles.sheafGlobalSectionsComplex (DivisorClass.Chern.Rational.BettiSheafComparison.rationalAbelianSingularResolution X))
  let S : AddCommGrpCat.{0} := H.obj
    (CycleClass.Geometric.FlasqueLowDegree.Cycles.sheafGlobalSectionsComplex (IntegerSingularSheafComparison.integerAbelianSingularResolution (ModuleCat.of ℤ ℚ) X))
  let T : AddCommGrpCat.{0} :=
    (Sheaf.functorH (Opens.grothendieckTopology X) (n + 1)).obj (DivisorClass.Chern.Rational.HolomorphicPeriod.rationalConstantAbelianSheaf X)
  let U : AddCommGrpCat.{0} :=
    (Sheaf.functorH (Opens.grothendieckTopology X) (n + 1)).obj
      (IntegerSingularSheafComparison.integerLocallyConstantAbelianSheaf (ModuleCat.of ℤ ℚ) X)
  let a : A ⟶ B := (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForgetHomologyIso Q (n + 1)).inv
  let b : B ⟶ C := H.map (ModuleForgetCocycleClasses.rationalIntegerAbelianCochainIso X).hom
  let e : C ≅ D := (Z.sc (n + 1)).mapHomologyIso IntegerSingularSheafComparison.integerModuleForget
  let c : C ⟶ S := H.map (DivisorClass.Chern.ModuleGlobalSectionsForget.moduleSingularToAbelianSections ℤ X (ModuleCat.of ℤ ℚ))
  let d : B ⟶ R := H.map (DivisorClass.Chern.ModuleGlobalSectionsForget.moduleSingularToAbelianSections ℚ X (ModuleCat.of ℚ ℚ))
  let f : R ⟶ S := H.map (((CycleClass.Geometric.FlasqueLowDegree.Cycles.sheafGlobalSections X).mapHomologicalComplex (.up ℕ)).map
    (RationalIntegerSheafComparison.rationalIntegerSingularSheafIso X).hom)
  let k : R ⟶ T := DivisorClass.Chern.Intrinsic.AugmentationNaturality.nativeSectionCohomologyMapOfZero (DivisorClass.Chern.Rational.BettiSheafComparison.rationalAbelianSingularResolution X)
    (DivisorClass.Chern.Rational.BettiSheafComparison.rationalAbelianSingularResolution_exact X) (DivisorClass.Chern.Rational.BettiSheafComparison.rationalConstantAbelianZeroIso X) n
  let j : S ⟶ U := DivisorClass.Chern.Intrinsic.AugmentationNaturality.nativeSectionCohomologyMapOfZero
    (IntegerSingularSheafComparison.integerAbelianSingularResolution (ModuleCat.of ℤ ℚ) X)
    (IntegerSingularSheafComparison.integerAbelianSingularResolution_exact (ModuleCat.of ℤ ℚ) X)
    (IntegerSingularSheafComparison.integerConstantAbelianZeroIso (ModuleCat.of ℤ ℚ) X) n
  let u : T ⟶ U := (Sheaf.functorH (Opens.grothendieckTopology X) (n + 1)).map
    (IntegralSheafCoefficients.originalRationalConstantIso X).inv
  let v : A ⟶ D := (ModuleForgetCocycleClasses.rationalIntegerCohomologyIso X (n + 1)).hom
  let q : A ⟶ T := (DivisorClass.Chern.Rational.BettiCechSheafComparison.rationalBettiCechSheafIso X n).hom
  let z : D ⟶ U := IntegerSingularSheafComparison.integerSingularBettiSheafMap (ModuleCat.of ℤ ℚ) X n
  have hv : v = a ≫ b ≫ e.hom := rfl
  have ha : a ≫ b = v ≫ e.inv := by
    have hcancel : (a ≫ b ≫ e.hom) ≫ e.inv = a ≫ b := by
      rw [Category.assoc, Category.assoc, e.hom_inv_id, Category.comp_id]
    exact hcancel.symm.trans (congrArg (fun w : A ⟶ D => w ≫ e.inv) hv.symm)
  have hb : d ≫ f = b ≫ c :=
    (H.map_comp _ _).symm.trans
      ((congrArg H.map (RationalIntegerSheafComparison.rationalIntegerSingularSheafIso_globalSections X)).trans (H.map_comp _ _))
  have hn : f ≫ j = k ≫ u := DivisorClass.Chern.Intrinsic.AugmentationNaturality.nativeSectionCohomologyMapOfZero_naturality
    (RationalIntegerSheafComparison.rationalIntegerSingularSheafIso X).hom
    (DivisorClass.Chern.Rational.BettiSheafComparison.rationalAbelianSingularResolution_exact X)
    (IntegerSingularSheafComparison.integerAbelianSingularResolution_exact (ModuleCat.of ℤ ℚ) X)
    (IntegralSheafCoefficients.originalRationalConstantIso X).inv (DivisorClass.Chern.Rational.BettiSheafComparison.rationalConstantAbelianZeroIso X)
    (IntegerSingularSheafComparison.integerConstantAbelianZeroIso (ModuleCat.of ℤ ℚ) X)
    (RationalIntegerSheafComparison.rationalIntegerSingularSheafIso_zero X) n
  have hq : q = a ≫ d ≫ k := DivisorClass.Chern.Intrinsic.BettiSheafMaps.rationalBettiCechSheafIso_hom_sections X n
  have hz : z = e.inv ≫ c ≫ j := integerSingularBettiSheafMap_hom_sections X (ModuleCat.of ℤ ℚ) n
  have hh : (a ≫ d ≫ k) ≫ u = v ≫ e.inv ≫ c ≫ j :=
    CoefficientComparisonDiagrams.three_comparison_squares a d k e.inv c j v b f u ha hb hn.symm
  exact (congrArg (fun w : D ⟶ U => v ≫ w) hz).trans
    (hh.symm.trans (congrArg (fun w : A ⟶ T => w ≫ u) hq.symm))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RationalIntegerBettiComparison

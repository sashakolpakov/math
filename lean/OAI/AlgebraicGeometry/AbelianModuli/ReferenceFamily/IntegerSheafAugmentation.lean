import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CoefficientSingularSheafNaturality
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntegerSingularSheafComparison
import OAI.AlgebraicGeometry.DivisorClass.Chern.ThomSourceOrientation

/-! # Integer Sheaf Augmentation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntegerSheafAugmentation

noncomputable section

/-! The integer-coefficient resolution identifies its degree-zero
cohomology through the original locally constant point functions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

open OAI.AlgebraicGeometry.DivisorClass.Chern.ThomSourceOrientation

variable {R : Type} [Ring R] (M : ModuleCat.{0} R) (X : TopCat.{0})

def coefficientSingularSheafAugmentation :
    LocallyConstantModuleSheaf.coefficientLocallyConstantSheaf M X ⟶ (CoefficientSingularSheafResolution.coefficientSingularSheafComplex M X).X 0 :=
  (sheafificationIso (LocallyConstantModuleSheaf.coefficientLocallyConstantSheaf M X)).hom ≫
    (presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} R)).map
      (LocallyConstantModuleSheaf.coefficientLocallyConstantAugmentation M X)

theorem coefficientSingularSheafAugmentation_hom :
    (coefficientSingularSheafAugmentation M X).hom =
      LocallyConstantModuleSheaf.coefficientLocallyConstantAugmentation M X ≫
        CategoryTheory.toSheafify (Opens.grothendieckTopology X)
          ((AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex M X).X 0) := by
  exact (CategoryTheory.toSheafify_naturality (Opens.grothendieckTopology X)
    (LocallyConstantModuleSheaf.coefficientLocallyConstantAugmentation M X)).symm

theorem coefficientLocallyConstantSheafZeroIso_augmentation [LocallyPathConnectedSpace X] :
    (CoefficientSingularSheafResolution.coefficientLocallyConstantSheafZeroIso M X).hom ≫
      (HodgeConjecture.DegreeTwo.ThomGoodShiftFlasque.Constructions.cochainZeroHomologyAugmentation (CoefficientSingularSheafResolution.coefficientSingularSheafComplex M X)).f 0 =
        coefficientSingularSheafAugmentation M X := by
  let K := AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex M X
  let F := presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} R)
  have hc := DivisorClass.Chern.ThomSourceOrientation.cochainLeftExactZeroHomologyIso_inclusion K F
  rw [DivisorClass.Chern.ThomSourceOrientation.cochainLeftExactZeroHomologyIso_hom_eq, AlgebraicTopology.Cohomology.Singular.LeftExactHomologyComposition.leftExactHomologyComparison_eq_mapHomologyIso] at hc
  have hi : ((K.sc 0).mapHomologyIso F).inv ≫
      (CochainComplex.isoHomologyπ₀ ((F.mapHomologicalComplex (.up ℕ)).obj K)).inv ≫
        ((F.mapHomologicalComplex (.up ℕ)).obj K).iCycles 0 =
      F.map (K.isoHomologyπ₀.inv ≫ K.iCycles 0) :=
    ((K.sc 0).mapHomologyIso F).inv_comp_eq.mpr hc.symm
  let S0 : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{0} R) :=
    LocallyConstantModuleSheaf.coefficientLocallyConstantSheaf M X
  let S1 : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{0} R) :=
    F.obj (LocallyConstantModuleSheaf.coefficientLocallyConstantPresheaf M X)
  let S2 : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{0} R) := F.obj (K.homology 0)
  let S3 : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{0} R) :=
    ((F.mapHomologicalComplex (.up ℕ)).obj K).homology 0
  let S4 : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{0} R) :=
    ((F.mapHomologicalComplex (.up ℕ)).obj K).X 0
  let e := CoefficientSingularSheafResolution.coefficientLocallyConstantPresheafZeroIso M X
  let b : S0 ⟶ S1 := (sheafificationIso (LocallyConstantModuleSheaf.coefficientLocallyConstantSheaf M X)).hom
  let a : S1 ⟶ S2 := F.map e.hom
  let c : S2 ⟶ S3 := ((K.sc 0).mapHomologyIso F).inv
  let d : S3 ⟶ S4 :=
    (CochainComplex.isoHomologyπ₀ ((F.mapHomologicalComplex (.up ℕ)).obj K)).inv ≫
      ((F.mapHomologicalComplex (.up ℕ)).obj K).iCycles 0
  let k : S2 ⟶ S4 := F.map (K.isoHomologyπ₀.inv ≫ K.iCycles 0)
  have hcd : c ≫ d = k := hi
  have hz := CoefficientSingularSheafNaturality.coefficientLocallyConstantPresheafZeroIso_augmentation X M
  have heq := congrArg (fun v : K.homology 0 ⟶ K.X 0 => e.hom ≫ v)
    (HodgeConjecture.DegreeTwo.ThomGoodShiftFlasque.Constructions.cochainZeroHomologyAugmentation_f_zero K)
  have hz' := heq.symm.trans hz
  have hak : a ≫ k = F.map (LocallyConstantModuleSheaf.coefficientLocallyConstantAugmentation M X) :=
    (F.map_comp e.hom (K.isoHomologyπ₀.inv ≫ K.iCycles 0)).symm.trans
      (congrArg F.map hz')
  have hh : (b ≫ a ≫ c) ≫ d = b ≫ F.map (LocallyConstantModuleSheaf.coefficientLocallyConstantAugmentation M X) :=
    (Category.assoc b (a ≫ c) d).trans
      ((congrArg (fun v : S1 ⟶ S4 => b ≫ v) (Category.assoc a c d)).trans
        ((congrArg (fun v : S2 ⟶ S4 => b ≫ a ≫ v) hcd).trans
          (congrArg (fun v : S1 ⟶ S4 => b ≫ v) hak)))
  rw [HodgeConjecture.DegreeTwo.ThomGoodShiftFlasque.Constructions.cochainZeroHomologyAugmentation_f_zero]
  exact hh

def integerAbelianConstantAugmentation (A : ModuleCat.{0} ℤ) :
    IntegerSingularSheafComparison.integerLocallyConstantAbelianSheaf A X ⟶ (IntegerSingularSheafComparison.integerAbelianSingularResolution A X).X 0 :=
  (IntegerSingularSheafComparison.integerCoefficientSheafForget X).map (coefficientSingularSheafAugmentation A X)

theorem integerAbelianConstantAugmentation_zeroIso (A : ModuleCat.{0} ℤ)
    [LocallyPathConnectedSpace X] :
    (IntegerSingularSheafComparison.integerConstantAbelianZeroIso A X).hom ≫
      (HodgeConjecture.DegreeTwo.ThomGoodShiftFlasque.Constructions.cochainZeroHomologyAugmentation (IntegerSingularSheafComparison.integerAbelianSingularResolution A X)).f 0 =
        integerAbelianConstantAugmentation X A := by
  let K := CoefficientSingularSheafResolution.coefficientSingularSheafComplex A X
  let G := IntegerSingularSheafComparison.integerCoefficientSheafForget X
  have hc := DivisorClass.Chern.ThomSourceOrientation.cochainLeftExactZeroHomologyIso_inclusion K G
  rw [DivisorClass.Chern.ThomSourceOrientation.cochainLeftExactZeroHomologyIso_hom_eq, AlgebraicTopology.Cohomology.Singular.LeftExactHomologyIso.leftExactHomologyComparison_eq_mapHomologyIso',
    ShortComplex.mapHomologyIso'_eq_mapHomologyIso] at hc
  have hi : ((K.sc 0).mapHomologyIso G).inv ≫
      (IntegerSingularSheafComparison.integerAbelianSingularResolution A X).isoHomologyπ₀.inv ≫
        (IntegerSingularSheafComparison.integerAbelianSingularResolution A X).iCycles 0 =
      G.map (K.isoHomologyπ₀.inv ≫ K.iCycles 0) :=
    ((K.sc 0).mapHomologyIso G).inv_comp_eq.mpr hc.symm
  let S0 : TopCat.Sheaf AddCommGrpCat.{0} X := G.obj (LocallyConstantModuleSheaf.coefficientLocallyConstantSheaf A X)
  let S1 : TopCat.Sheaf AddCommGrpCat.{0} X := G.obj (K.homology 0)
  let S2 : TopCat.Sheaf AddCommGrpCat.{0} X := (IntegerSingularSheafComparison.integerAbelianSingularResolution A X).homology 0
  let S3 : TopCat.Sheaf AddCommGrpCat.{0} X := (IntegerSingularSheafComparison.integerAbelianSingularResolution A X).X 0
  let e := CoefficientSingularSheafResolution.coefficientLocallyConstantSheafZeroIso A X
  let a : S0 ⟶ S1 := G.map e.hom
  let c : S1 ⟶ S2 := ((K.sc 0).mapHomologyIso G).inv
  let d : S2 ⟶ S3 :=
    (IntegerSingularSheafComparison.integerAbelianSingularResolution A X).isoHomologyπ₀.inv ≫
      (IntegerSingularSheafComparison.integerAbelianSingularResolution A X).iCycles 0
  let k : S1 ⟶ S3 := G.map (K.isoHomologyπ₀.inv ≫ K.iCycles 0)
  have hcd : c ≫ d = k := hi
  have hz := coefficientLocallyConstantSheafZeroIso_augmentation A X
  have heq := congrArg (fun v : K.homology 0 ⟶ K.X 0 => e.hom ≫ v)
    (HodgeConjecture.DegreeTwo.ThomGoodShiftFlasque.Constructions.cochainZeroHomologyAugmentation_f_zero K)
  have hz' := heq.symm.trans hz
  have hak : a ≫ k = G.map (coefficientSingularSheafAugmentation A X) :=
    (G.map_comp e.hom (K.isoHomologyπ₀.inv ≫ K.iCycles 0)).symm.trans
      (congrArg G.map hz')
  have hh : (a ≫ c) ≫ d = G.map (coefficientSingularSheafAugmentation A X) :=
    (Category.assoc a c d).trans ((congrArg (fun v : S1 ⟶ S3 => a ≫ v) hcd).trans hak)
  rw [HodgeConjecture.DegreeTwo.ThomGoodShiftFlasque.Constructions.cochainZeroHomologyAugmentation_f_zero]
  exact hh

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntegerSheafAugmentation

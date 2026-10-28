import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntegerSingularSheafComparison
import OAI.AlgebraicGeometry.DivisorClass.Chern.RestrictionCochainEvaluation
import OAI.AlgebraicGeometry.DivisorClass.Chern.ModuleGlobalSectionsForget
import OAI.AlgebraicGeometry.SheafCohomology.Cech.PositiveCycleHomology
import OAI.AlgebraicTopology.Cohomology.Singular.LeftExactHomologyComposition

/-! # Module Forget Cocycle Classes -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ModuleForgetCocycleClasses

noncomputable section

section

/-! The literal rational singular cochains, with scalars forgotten to
integers. The comparison preserves the value on every original simplex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
open scoped Simplicial

open OAI.AlgebraicTopology.Cohomology.Singular.LeftExactHomologyComposition

def rationalIntegerAbelianCochainIso (X : TopCat.{0}) :
    (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForget.mapHomologicalComplex (.up ℕ)).obj (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X) ≅
      (IntegerSingularSheafComparison.integerModuleForget.mapHomologicalComplex (.up ℕ)).obj
        (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℤ ℚ) X) :=
  (IntegerSingularSheafComparison.integerModuleForget.mapHomologicalComplex (.up ℕ)).mapIso
    (AlgebraicTopology.Cohomology.Singular.Chains.singularCochainsRestrictScalarsIso (algebraMap ℤ ℚ) (ModuleCat.of ℚ ℚ) X)

theorem rationalIntegerAbelianCochainIso_evaluation (X : TopCat.{0}) {n : ℕ}
    (s : (TopCat.toSSet.obj X) _⦋n⦌)
    (c : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).X n) :
    AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation (TopCat.toSSet.obj X) (ModuleCat.of ℤ ℚ) s
      ((rationalIntegerAbelianCochainIso X).hom.f n c) =
        AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation (TopCat.toSSet.obj X) (ModuleCat.of ℚ ℚ) s c :=
  ConcreteCategory.congr_hom
    (DivisorClass.Chern.RestrictionCochainEvaluation.singularCochainsRestrictScalarsIso_hom_evaluation
      (algebraMap ℤ ℚ) (ModuleCat.of ℚ ℚ) X s) c

theorem rationalIntegerAbelianCochainIso_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) :
    (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForget.mapHomologicalComplex (.up ℕ)).map
        (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ) f) ≫ (rationalIntegerAbelianCochainIso X).hom =
      (rationalIntegerAbelianCochainIso Y).hom ≫
        (IntegerSingularSheafComparison.integerModuleForget.mapHomologicalComplex (.up ℕ)).map
          (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℤ ℚ) f) := by
  have h := AlgebraicTopology.Cohomology.Singular.Chains.singularCochainsRestrictScalarsIso_naturality
    (algebraMap ℤ ℚ) (ModuleCat.of ℚ ℚ) f
  ext n : 1
  apply ConcreteCategory.hom_ext
  intro c
  have hn := congrArg (fun g => g.f n) h
  have he := ConcreteCategory.congr_hom hn c
  exact he

def rationalIntegerPresheafIso (X : TopCat.{0}) :
    DivisorClass.Chern.ModuleSheafificationForget.moduleForgetPresheafComplex ℚ X (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X) ≅
      DivisorClass.Chern.ModuleSheafificationForget.moduleForgetPresheafComplex ℤ X (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℤ ℚ) X) :=
  HomologicalComplex.Hom.isoOfComponents (fun n =>
    NatIso.ofComponents (fun U =>
      (HomologicalComplex.eval AddCommGrpCat.{0} (.up ℕ) n).mapIso
        (rationalIntegerAbelianCochainIso (TopCat.of U.unop))) (by
      intro U V i
      exact congrArg (fun g => g.f n)
        (rationalIntegerAbelianCochainIso_naturality ((Opens.toTopCat X).map i.unop)))) (by
    intro i j _
    apply NatTrans.ext
    funext U
    exact (rationalIntegerAbelianCochainIso (TopCat.of U.unop)).hom.comm i j)

def rationalIntegerCohomologyIso (X : TopCat.{0}) (n : ℕ) :
    AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForget.obj (AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X n) ≅
      IntegerSingularSheafComparison.integerModuleForget.obj (AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℤ ℚ) X n) :=
  (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForgetHomologyIso (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X) n).symm ≪≫
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{0} (.up ℕ) n).mapIso
      (rationalIntegerAbelianCochainIso X) ≪≫
    (((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℤ ℚ) X).sc n).mapHomologyIso IntegerSingularSheafComparison.integerModuleForget)

theorem rationalIntegerAbelianCochainIso_locallyConstant
    (X : TopCat.{0}) (q : LocallyConstant X ℚ) :
    (rationalIntegerAbelianCochainIso X).hom.f 0
        (AlgebraicTopology.Cohomology.Singular.Augmentation.locallyConstantToSingularZero (ModuleCat.of ℚ ℚ) X q) =
      AlgebraicTopology.Cohomology.Singular.Augmentation.locallyConstantToSingularZero (ModuleCat.of ℤ ℚ) X q := by
  let cQ : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).X 0 :=
    AlgebraicTopology.Cohomology.Singular.Augmentation.locallyConstantToSingularZero (ModuleCat.of ℚ ℚ) X q
  let cI : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℤ ℚ) X).X 0 :=
    (rationalIntegerAbelianCochainIso X).hom.f 0 cQ
  change cI = AlgebraicTopology.Cohomology.Singular.Augmentation.locallyConstantToSingularZero (ModuleCat.of ℤ ℚ) X q
  apply (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso (ModuleCat.of ℤ ℚ) X).toLinearEquiv.injective
  ext x
  let s := TopCat.toSSetObj₀Equiv.symm x
  have hI := (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso_apply (ModuleCat.of ℤ ℚ) X cI x).trans
    (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso_hom_apply (TopCat.toSSet.obj X) (ModuleCat.of ℤ ℚ) cI s)
  have hQ := (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso_apply (ModuleCat.of ℚ ℚ) X cQ x).trans
    (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso_hom_apply (TopCat.toSSet.obj X) (ModuleCat.of ℚ ℚ) cQ s)
  exact hI.trans ((rationalIntegerAbelianCochainIso_evaluation X s cQ).trans
    (hQ.symm.trans ((AlgebraicTopology.Cohomology.Singular.Augmentation.locallyConstantToSingularZero_apply (ModuleCat.of ℚ ℚ) X q x).trans
      (AlgebraicTopology.Cohomology.Singular.Augmentation.locallyConstantToSingularZero_apply (ModuleCat.of ℤ ℚ) X q x).symm)))

end

/-! Forgetting module scalars preserves the class of the same cocycle.
The comparison is expressed through the original categorical cycle inclusion. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open OAI.AlgebraicTopology.Cohomology.Singular.LeftExactHomologyComposition
open OAI.AlgebraicGeometry.SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology

variable {R : Type} [Ring R]

def moduleForgetCocycleClass (K : CochainComplex (ModuleCat.{0} R) ℕ)
    (n : ℕ) (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles K (n + 1)) :
    (((forget₂ (ModuleCat.{0} R) AddCommGrpCat.{0}).mapHomologicalComplex (.up ℕ)).obj K).homology
      (n + 1) :=
  (((forget₂ (ModuleCat.{0} R) AddCommGrpCat.{0}).mapHomologicalComplex (.up ℕ)).obj K).homologyπ
    (n + 1) (SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.abCyclesMk n _ c.val ((AlgebraicTopology.Cohomology.Singular.Representatives.mem_cochainCocycles_iff K (n + 1) c.val).mp c.property))

theorem moduleForgetCocycleClass_map (K : CochainComplex (ModuleCat.{0} R) ℕ)
    (n : ℕ) (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles K (n + 1)) :
    (((K.sc (n + 1)).mapHomologyIso (forget₂ (ModuleCat.{0} R) AddCommGrpCat.{0})).hom)
        (moduleForgetCocycleClass K n c) = AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass K (n + 1) c := by
  let G := forget₂ (ModuleCat.{0} R) AddCommGrpCat.{0}
  let L := (G.mapHomologicalComplex (.up ℕ)).obj K
  let S := K.sc (n + 1)
  let z := SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.abCyclesMk n L c.val ((AlgebraicTopology.Cohomology.Singular.Representatives.mem_cochainCocycles_iff K (n + 1) c.val).mp c.property)
  have hz : (AlgebraicTopology.Cohomology.Singular.LeftExactHomology.leftExactCyclesIso S G).hom z = (K.sc (n + 1)).moduleCatCyclesIso.inv c := by
    apply (ModuleCat.mono_iff_injective (K.iCycles (n + 1))).mp inferInstance
    have hh := ConcreteCategory.congr_hom (AlgebraicTopology.Cohomology.Singular.LeftExactHomology.leftExactCyclesIso_hom_iCycles S G) z
    change (K.iCycles (n + 1)) ((AlgebraicTopology.Cohomology.Singular.LeftExactHomology.leftExactCyclesIso S G).hom z) = (L.iCycles (n + 1)) z at hh
    have hzval : (L.iCycles (n + 1)) z = c.val :=
      SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.i_abCyclesMk n L c.val ((AlgebraicTopology.Cohomology.Singular.Representatives.mem_cochainCocycles_iff K (n + 1) c.val).mp c.property)
    have hk := ConcreteCategory.congr_hom ((K.sc (n + 1)).moduleCatCyclesIso_inv_iCycles) c
    change (K.iCycles (n + 1)) ((K.sc (n + 1)).moduleCatCyclesIso.inv c) = c.val at hk
    exact hh.trans (hzval.trans hk.symm)
  have h := ConcreteCategory.congr_hom (AlgebraicTopology.Cohomology.Singular.LeftExactHomology.homologyπ_leftExactHomologyComparison S G) z
  rw [AlgebraicTopology.Cohomology.Singular.LeftExactHomologyIso.leftExactHomologyComparison_eq_mapHomologyIso',
    ShortComplex.mapHomologyIso'_eq_mapHomologyIso] at h
  change ((S.mapHomologyIso G).hom) (L.homologyπ (n + 1) z) =
    (K.homologyπ (n + 1)) ((AlgebraicTopology.Cohomology.Singular.LeftExactHomology.leftExactCyclesIso S G).hom z) at h
  exact h.trans ((congrArg (K.homologyπ (n + 1)) hz).trans
    (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_eq_homologyπ K (n + 1) c).symm)

def rationalIntegerCocycle (X : TopCat.{0}) (n : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of ℚ ℚ) X n) :
    AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of ℤ ℚ) X n :=
  AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap
    (AlgebraicTopology.Cohomology.Singular.Chains.singularCochainsRestrictScalarsIso (algebraMap ℤ ℚ) (ModuleCat.of ℚ ℚ) X).hom n
      ⟨c.val, c.property⟩

theorem rationalIntegerCohomologyIso_class (X : TopCat.{0}) (n : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of ℚ ℚ) X (n + 1)) :
    (rationalIntegerCohomologyIso X (n + 1)).hom
        (AlgebraicTopology.Cohomology.Singular.Representatives.singularClass (ModuleCat.of ℚ ℚ) X (n + 1) c) =
      AlgebraicTopology.Cohomology.Singular.Representatives.singularClass (ModuleCat.of ℤ ℚ) X (n + 1) (rationalIntegerCocycle X (n + 1) c) := by
  have hcQ := moduleForgetCocycleClass_map (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X) n c
  have hcZ := moduleForgetCocycleClass_map (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℤ ℚ) X) n
    (rationalIntegerCocycle X (n + 1) c)
  have hm : HomologicalComplex.homologyMap (rationalIntegerAbelianCochainIso X).hom (n + 1)
        (moduleForgetCocycleClass (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X) n c) =
      moduleForgetCocycleClass (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℤ ℚ) X) n
        (rationalIntegerCocycle X (n + 1) c) :=
    SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.homologyMap_abCyclesMk n (rationalIntegerAbelianCochainIso X).hom c.val
      ((AlgebraicTopology.Cohomology.Singular.Representatives.mem_cochainCocycles_iff _ _ _).mp c.property)
      ((AlgebraicTopology.Cohomology.Singular.Representatives.mem_cochainCocycles_iff _ _ _).mp (rationalIntegerCocycle X (n + 1) c).property)
  change (rationalIntegerCohomologyIso X (n + 1)).hom (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (n + 1) c) = _
  rw [← hcQ]
  change (((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℤ ℚ) X).sc (n + 1)).mapHomologyIso IntegerSingularSheafComparison.integerModuleForget).hom
    (HomologicalComplex.homologyMap (rationalIntegerAbelianCochainIso X).hom (n + 1)
      ((AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForgetHomologyIso (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X) (n + 1)).inv
        ((AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForgetHomologyIso (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X) (n + 1)).hom
          (moduleForgetCocycleClass (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X) n c)))) = _
  rw [Iso.hom_inv_id_apply, hm]
  exact hcZ

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ModuleForgetCocycleClasses

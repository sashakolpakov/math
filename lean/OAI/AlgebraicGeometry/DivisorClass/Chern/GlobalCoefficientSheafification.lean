import OAI.AlgebraicGeometry.DivisorClass.Chern.ModuleGlobalSectionsForget
import OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.ComplexSheafMap
import OAI.AlgebraicTopology.Cohomology.Singular.LeftExactHomologyComposition

/-! # Global Coefficient Sheafification -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.GlobalCoefficientSheafification

noncomputable section

section

/-! Original global singular sheafification commutes with the original rational coefficient cochain map. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open OAI.AlgebraicTopology.Cohomology.Singular.LeftExactHomologyComposition

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem moduleSingularToAbelianSections_rationalComplex (X : TopCat.{0}) :
    ModuleGlobalSectionsForget.moduleSingularToAbelianSections ℚ X (ModuleCat.of ℚ ℚ) ≫
        ((CycleClass.Geometric.FlasqueLowDegree.Cycles.sheafGlobalSections X).mapHomologicalComplex (.up ℕ)).map (Rational.ComplexSheafMap.rationalComplexSingularSheafMap X) =
      Rational.ComplexPresheaf.rationalToComplexAbelianCochainMap X ≫ ModuleGlobalSectionsForget.moduleSingularToAbelianSections ℂ X (ModuleCat.of ℂ ℂ) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro c
  let incl := Opens.inclusion' (⊤ : Opens X)
  let qtop := (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ) incl).f n c
  let etaC := CategoryTheory.toSheafify (Opens.grothendieckTopology X)
    ((AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℂ ℂ) X).X n)
  have hu := ConcreteCategory.congr_hom (C := AddCommGrpCat.{0})
    (congrArg (fun f => f.app (op (⊤ : Opens X))) (Rational.ComplexSheafMap.rationalComplexSingularSheafMap_unit X n)) qtop
  have hn := ConcreteCategory.congr_hom (C := ModuleCat.{0} ℚ)
    (congrArg (fun f => f.f n) (Rational.ComplexCochains.rationalToComplexCochainMap_naturality incl)) c
  change (Rational.ComplexCochains.rationalToComplexCochainMap (TopCat.of (⊤ : Opens X))).f n qtop =
    (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℂ ℂ) incl).f n ((Rational.ComplexCochains.rationalToComplexCochainMap X).f n c) at hn
  change (((Rational.ComplexSheafMap.rationalComplexSingularSheafMap X).f n).hom.app (op (⊤ : Opens X)))
      ((AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.singularCochainsToSheafSections (ModuleCat.of ℚ ℚ) X).f n c) =
    etaC.app (op (⊤ : Opens X)) ((Rational.ComplexCochains.rationalToComplexCochainMap (TopCat.of (⊤ : Opens X))).f n qtop) at hu
  exact hu.trans (congrArg (fun v => etaC.app (op (⊤ : Opens X)) v) hn)

end

/-! The additive homology map is exactly the original rational-to-complex cohomology inclusion. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open OAI.AlgebraicTopology.Cohomology.Singular.LeftExactHomologyComposition

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem complexForgetHomologyIso_restrict (K : CochainComplex (ModuleCat.{0} ℂ) ℕ) (n : ℕ) :
    (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForgetHomologyIso
      (((ModuleCat.restrictScalars (algebraMap ℚ ℂ)).mapHomologicalComplex (.up ℕ)).obj K) n).hom ≫
        AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForget.map (((K.sc n).mapHomologyIso (ModuleCat.restrictScalars (algebraMap ℚ ℂ))).hom) =
      (ModuleGlobalSectionsForget.complexForgetHomologyIso K n).hom := by
  have h := AlgebraicTopology.Cohomology.Singular.LeftExactHomologyComposition.leftExactHomologyComparison_comp (K.sc n) (ModuleCat.restrictScalars (algebraMap ℚ ℂ)) AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForget
  simp only [AlgebraicTopology.Cohomology.Singular.LeftExactHomologyIso.leftExactHomologyComparison_eq_mapHomologyIso', ShortComplex.mapHomologyIso'_eq_mapHomologyIso] at h
  exact h

theorem rationalToComplexAbelianCochainMap_homology (X : TopCat.{0}) (n : ℕ) :
    HomologicalComplex.homologyMap (Rational.ComplexPresheaf.rationalToComplexAbelianCochainMap X) n ≫
        (ModuleGlobalSectionsForget.complexForgetHomologyIso (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℂ ℂ) X) n).hom =
      (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForgetHomologyIso (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X) n).hom ≫
        AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForget.map (AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology X n) := by
  rw [← complexForgetHomologyIso_restrict, ← Category.assoc]
  erw [AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForgetHomologyIso_naturality (Rational.ComplexCochains.rationalToComplexCochainMap X) n]
  rw [Category.assoc, ← Functor.map_comp, Rational.ComplexCochains.rationalToComplexCochainMap_homology]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.GlobalCoefficientSheafification

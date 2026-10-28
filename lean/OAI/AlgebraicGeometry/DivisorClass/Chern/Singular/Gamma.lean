import OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.CochainForget
import OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.BettiCechSheafComparison
import OAI.AlgebraicGeometry.DivisorClass.Chern.Singular.GammaAugmentation

/-! # Gamma -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Singular.Gamma

noncomputable section

/-! The native global-section class is induced by the actual original singular cocycle. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicGeometry.SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (X : TopCat.{0}) (n : ℕ)

theorem rationalSingularToGamma_closed (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of ℚ ℚ) X (n + 1)) :
    (FlasqueCechD.abelianDerivedSectionsComplex (Rational.BettiSheafComparison.rationalAbelianSingularResolution X)).d (n + 1) (n + 2)
      ((GammaAugmentation.rationalSingularToGamma X).f (n + 1) c.val) = 0 := by
  have hc := (AlgebraicTopology.Cohomology.Singular.Representatives.mem_cochainCocycles_iff (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X) (n + 1) c.val).mp c.property
  have h := ConcreteCategory.congr_hom ((GammaAugmentation.rationalSingularToGamma X).comm (n + 1) (n + 2)) c.val
  change (FlasqueCechD.abelianDerivedSectionsComplex (Rational.BettiSheafComparison.rationalAbelianSingularResolution X)).d (n + 1) (n + 2)
      ((GammaAugmentation.rationalSingularToGamma X).f (n + 1) c.val) =
    (GammaAugmentation.rationalSingularToGamma X).f (n + 2)
      ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).d (n + 1) (n + 2) c.val) at h
  rw [hc, map_zero] at h
  exact h

def rationalSingularGammaClass (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of ℚ ℚ) X (n + 1)) :
    (FlasqueCechD.abelianDerivedSectionsComplex (Rational.BettiSheafComparison.rationalAbelianSingularResolution X)).homology (n + 1) :=
  (FlasqueCechD.abelianDerivedSectionsComplex (Rational.BettiSheafComparison.rationalAbelianSingularResolution X)).homologyπ (n + 1)
    (SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.abCyclesMk n _ ((GammaAugmentation.rationalSingularToGamma X).f (n + 1) c.val) (rationalSingularToGamma_closed X n c))

theorem rationalSingularGammaClass_map (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of ℚ ℚ) X (n + 1)) :
    HomologicalComplex.homologyMap (GammaAugmentation.rationalSingularToGamma X) (n + 1)
        (Rational.CochainForget.rationalForgetCycleClass (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X) n c) =
      rationalSingularGammaClass X n c :=
  SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.homologyMap_abCyclesMk n (GammaAugmentation.rationalSingularToGamma X) c.val
    ((AlgebraicTopology.Cohomology.Singular.Representatives.mem_cochainCocycles_iff (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X) (n + 1) c.val).mp c.property)
    (rationalSingularToGamma_closed X n c)

variable [MetrizableSpace X] [StronglyLocallyContractibleSpace X] [LocallyPathConnectedSpace X]

theorem rationalBettiCechSheafIso_hom :
    (Rational.BettiCechSheafComparison.rationalBettiCechSheafIso X n).hom =
      (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForgetHomologyIso (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X) (n + 1)).inv ≫
        HomologicalComplex.homologyMap (GammaAugmentation.rationalSingularToGamma X) (n + 1) ≫
          (GammaSectionsComparison.nativeFlasqueCohomologyIsoOfZero (Rational.BettiSheafComparison.rationalAbelianSingularResolution X)
            (Rational.BettiSheafComparison.rationalAbelianSingularResolution_flasque X) (Rational.BettiSheafComparison.rationalAbelianSingularResolution_exact X)
            n (Rational.BettiSheafComparison.rationalConstantAbelianZeroIso X)).hom := by
  let : MetricSpace X := metrizableSpaceMetric X
  let f := AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.singularCochainsToSheafSections (ModuleCat.of ℚ ℚ) X
  have h := AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForgetHomologyIso_naturality f (n + 1)
  have hi : AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForget.map (HomologicalComplex.homologyMap f (n + 1)) ≫
        (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForgetHomologyIso (AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.singularSheafGlobalSections (ModuleCat.of ℚ ℚ) X) (n + 1)).inv =
      (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForgetHomologyIso (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X) (n + 1)).inv ≫
        HomologicalComplex.homologyMap ((AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForget.mapHomologicalComplex (.up ℕ)).map f) (n + 1) := by
    rw [(AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForgetHomologyIso (AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.singularSheafGlobalSections (ModuleCat.of ℚ ℚ) X)
      (n + 1)).comp_inv_eq, Category.assoc, h]
    simp
  unfold Rational.BettiCechSheafComparison.rationalBettiCechSheafIso AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalSectionsForgetHomologyIso
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    AlgebraicTopology.Cohomology.Singular.ParacompactComparison.paracompactSingularCohomologySheafSectionsIso_hom]
  simp only [Category.assoc]
  erw [← Category.assoc (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForget.map (HomologicalComplex.homologyMap f (n + 1)))
    (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForgetHomologyIso (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalSheafSectionsComplex ⊤ (HodgeConjecture.DegreeTwo.SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex X)) (n + 1)).inv]
  erw [hi]
  simp only [Category.assoc]
  rw [GammaAugmentation.rationalSingularToGamma, HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp]
  rfl

theorem rationalBettiCechSheafEquiv_class (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of ℚ ℚ) X (n + 1)) :
    Rational.BettiCechSheafComparison.rationalBettiCechSheafEquiv X n (AlgebraicTopology.Cohomology.Singular.Representatives.singularClass (ModuleCat.of ℚ ℚ) X (n + 1) c) =
      (GammaSectionsComparison.nativeFlasqueCohomologyIsoOfZero (Rational.BettiSheafComparison.rationalAbelianSingularResolution X)
        (Rational.BettiSheafComparison.rationalAbelianSingularResolution_flasque X) (Rational.BettiSheafComparison.rationalAbelianSingularResolution_exact X)
        n (Rational.BettiSheafComparison.rationalConstantAbelianZeroIso X)).hom (rationalSingularGammaClass X n c) := by
  change (Rational.BettiCechSheafComparison.rationalBettiCechSheafIso X n).hom _ = _
  rw [rationalBettiCechSheafIso_hom]
  have hc : (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForgetHomologyIso (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X) (n + 1)).inv
      (AlgebraicTopology.Cohomology.Singular.Representatives.singularClass (ModuleCat.of ℚ ℚ) X (n + 1) c) =
    Rational.CochainForget.rationalForgetCycleClass (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X) n c := by
    rw [← Rational.CochainForget.rationalForgetCycleClass_map]
    exact Iso.hom_inv_id_apply _ _
  change (GammaSectionsComparison.nativeFlasqueCohomologyIsoOfZero (Rational.BettiSheafComparison.rationalAbelianSingularResolution X)
      (Rational.BettiSheafComparison.rationalAbelianSingularResolution_flasque X) (Rational.BettiSheafComparison.rationalAbelianSingularResolution_exact X)
      n (Rational.BettiSheafComparison.rationalConstantAbelianZeroIso X)).hom
    (HomologicalComplex.homologyMap (GammaAugmentation.rationalSingularToGamma X) (n + 1)
    ((AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForgetHomologyIso (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X) (n + 1)).inv
      (AlgebraicTopology.Cohomology.Singular.Representatives.singularClass (ModuleCat.of ℚ ℚ) X (n + 1) c))) = _
  rw [hc, rationalSingularGammaClass_map]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Singular.Gamma

import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RationalSmoothCechAugmentation
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RationalCohomologyMap
import OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.Obj

/-! # Rational Cech Class -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RationalCechClass.CM.Construction

noncomputable section

/-! The rational singular class constructed by Čech descent has the
expected native complex smooth Čech class. -/

open _root_.CategoryTheory _root_.TopologicalSpace

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {I : Type} (U : I → Opens M)

theorem rationalCechClass_augmentation (hcover : ∀ x : M, ∃ i, x ∈ U i)
    (n : ℕ) (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles
      (DivisorClass.Chern.Rational.Cech.RationalCech.cechComplex
        (DivisorClass.Chern.Cech.Obj.RationalCech.locallyConstantPresheaf (TopCat.of M)) U) n) :
    HomologicalComplex.homologyMap
      (DivisorClass.Chern.Rational.CechComparison.RationalCech.globalSingularCechAugmentation (TopCat.of M) U (ModuleCat.of ℚ ℚ)) n
      (DivisorClass.Chern.Cech.Obj.RationalCech.singularClassOfCechCocycle (TopCat.of M) U hcover n c) =
    AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (DivisorClass.Chern.Rational.CechComparison.RationalCech.singularCechTotal (TopCat.of M) U (ModuleCat.of ℚ ℚ)) n
      (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (DivisorClass.Chern.Cech.Obj.RationalCech.locallyConstantCechToTotal (TopCat.of M) U) n c) := by
  let e := DivisorClass.Chern.Rational.CechComparison.RationalCech.singularCechCohomologyIso (TopCat.of M) U hcover n
  have h := e.inv_hom_id_apply
    (HomologicalComplex.homologyMap
      (DivisorClass.Chern.Cech.Obj.RationalCech.locallyConstantCechToTotal (TopCat.of M) U) n
      (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ n c))
  exact h.trans (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality
    (DivisorClass.Chern.Cech.Obj.RationalCech.locallyConstantCechToTotal (TopCat.of M) U) n c)

theorem rationalSmoothCechClass_of_cocycle (hcover : ∀ x : M, ∃ i, x ∈ U i)
    (n : ℕ) (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles
      (DivisorClass.Chern.Rational.Cech.RationalCech.cechComplex
        (DivisorClass.Chern.Cech.Obj.RationalCech.locallyConstantPresheaf (TopCat.of M)) U) n) :
    HomologicalComplex.homologyMap (AlgebraicTopology.Cohomology.Singular.SmoothCechDoubleComplex.globalManifoldSmoothCechAugmentation E M U (ModuleCat.of ℂ ℂ)) n
      (RationalCohomologyMap.CM.Construction.rationalComplexCohomologyMap (RationalSmoothCech.CM.Construction.rationalSmoothCochainMap E M) n
        (DivisorClass.Chern.Cech.Obj.RationalCech.singularClassOfCechCocycle (TopCat.of M) U hcover n c)) =
    AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.SmoothCechDoubleComplex.manifoldSmoothCechTotal E M U (ModuleCat.of ℂ ℂ)) n
      (RationalCohomologyMap.CM.Construction.rationalComplexCocycleMap (RationalSmoothCechAugmentation.CM.Construction.rationalSmoothCechTotalMap E M U) n
        (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (DivisorClass.Chern.Cech.Obj.RationalCech.locallyConstantCechToTotal (TopCat.of M) U) n c)) := by
  have hnat := RationalCohomologyMap.CM.Construction.rationalComplexCohomologyMap_naturality
    (RationalSmoothCech.CM.Construction.rationalSmoothCochainMap E M) (RationalSmoothCechAugmentation.CM.Construction.rationalSmoothCechTotalMap E M U)
    (DivisorClass.Chern.Rational.CechComparison.RationalCech.globalSingularCechAugmentation (TopCat.of M) U (ModuleCat.of ℚ ℚ))
    (AlgebraicTopology.Cohomology.Singular.SmoothCechDoubleComplex.globalManifoldSmoothCechAugmentation E M U (ModuleCat.of ℂ ℂ))
    (RationalSmoothCechAugmentation.CM.Construction.rationalSmoothCechTotalMap_global E M U) n
    (DivisorClass.Chern.Cech.Obj.RationalCech.singularClassOfCechCocycle (TopCat.of M) U hcover n c)
  have hQ := rationalCechClass_augmentation M U hcover n c
  have hC := RationalCohomologyMap.CM.Construction.rationalComplexCohomologyMap_class (RationalSmoothCechAugmentation.CM.Construction.rationalSmoothCechTotalMap E M U) n
    (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (DivisorClass.Chern.Cech.Obj.RationalCech.locallyConstantCechToTotal (TopCat.of M) U) n c)
  exact hnat.symm.trans
    ((congrArg (RationalCohomologyMap.CM.Construction.rationalComplexCohomologyMap (RationalSmoothCechAugmentation.CM.Construction.rationalSmoothCechTotalMap E M U) n) hQ).trans hC)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RationalCechClass.CM.Construction

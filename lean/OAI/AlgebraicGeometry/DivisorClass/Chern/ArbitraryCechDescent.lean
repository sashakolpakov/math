import OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.Descent

/-! # Arbitrary Cech Descent -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.ArbitraryCechDescent

noncomputable section

/-! Every rational Cech two-cocycle admits compatible actual singular descent. -/

open _root_.CategoryTheory _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}} {I : Type} (U : I → Opens X)
  (hU : ∀ x : X, ∃ i, x ∈ U i)
  (k : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (Rational.Cech.RationalCech.cechComplex (Cech.Obj.RationalCech.locallyConstantPresheaf X) U) 2)

theorem exists_singularDescent_for_cechCocycle :
    ∃ (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of ℚ ℚ) X 2) (d : Singular.CechDescent.SingularCechDescentData c U),
      AlgebraicTopology.Cohomology.Singular.Representatives.singularClass (ModuleCat.of ℚ ℚ) X 2 c = Cech.Obj.RationalCech.singularClassOfCechCocycle X U hU 2 k ∧
      Cech.Obj.RationalCech.locallyConstantCechEvaluation X U 2 k.val =
        -Rational.Cech.RationalCech.cechDelta ((AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X).X 0) U 1 d.horizontal := by
  obtain ⟨c, hc⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.singularClass_surjective (ModuleCat.of ℚ ℚ) X 2
    (Cech.Obj.RationalCech.singularClassOfCechCocycle X U hU 2 k)
  have he : HomologicalComplex.homologyMap (Cech.Obj.RationalCech.locallyConstantCechToTotal X U) 2
      (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (Rational.Cech.RationalCech.cechComplex (Cech.Obj.RationalCech.locallyConstantPresheaf X) U) 2 k) =
    HomologicalComplex.homologyMap (Rational.CechComparison.RationalCech.globalSingularCechAugmentation X U (ModuleCat.of ℚ ℚ)) 2
      (AlgebraicTopology.Cohomology.Singular.Representatives.singularClass (ModuleCat.of ℚ ℚ) X 2 c) := by
    rw [hc]
    change _ = (Rational.CechComparison.RationalCech.singularCechCohomologyIso X U hU 2).hom
      ((Rational.CechComparison.RationalCech.singularCechCohomologyIso X U hU 2).inv
        (HomologicalComplex.homologyMap (Cech.Obj.RationalCech.locallyConstantCechToTotal X U) 2
          (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (Rational.Cech.RationalCech.cechComplex (Cech.Obj.RationalCech.locallyConstantPresheaf X) U) 2 k)))
    exact ((Rational.CechComparison.RationalCech.singularCechCohomologyIso X U hU 2).inv_hom_id_apply _).symm
  rw [AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality, AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality] at he
  obtain ⟨b, hb⟩ := (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_eq_iff_exists_succ
    (Rational.CechComparison.RationalCech.singularCechTotal X U (ModuleCat.of ℚ ℚ)) 1 _ _).mp he
  exact ⟨c, Cech.Descent.singularCechDescentOfBoundary c k b hb, hc,
    Cech.Descent.singularCechDescentOfBoundary_cocycle c k b hb⟩

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.ArbitraryCechDescent

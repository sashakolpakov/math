import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExteriorCupSmallEvaluation
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RationalizedFunctionalExt

/-! # Exterior Cup Cross Evaluation -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExteriorCupCrossEvaluation.Constructions

noncomputable section

/-!
# DegreeTwo: exact evaluation of the supported exterior cup on cross products

The finite representative calculation determines the whole rational
homology functional. Combining it with the actual relative product
retraction gives the product of the two original relative evaluations.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false

variable (X Y : TopCat.{0}) (A : Set X) (B : Set Y) (hA : IsOpen A) (hB : IsOpen B) (p q : ℕ)

theorem relativeExteriorCup_evaluation_whitney
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) p)
    (d : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) Y B) q)
    (z : CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ (TopCat.of (X×Y)) (RelativeCrossSupport.Constructions.crossSupportComplement X Y A B) (p+q)) :
    CycleClass.Geometric.RelativeChainD.Cycles.relativeHomologyEvaluation (ModuleCat.of ℚ ℚ) (TopCat.of (X×Y))
      (RelativeCrossSupport.Constructions.crossSupportComplement X Y A B) (p+q)
      (ExteriorCupSmallEvaluation.Constructions.relativeExteriorCup X Y A B hA hB p q (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ p c) (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ q d)) z =
    RelativeTensorHomology.Constructions.relativeTensorHomologyFunctional X Y A B p q c d
      (SmallProductComparison.Constructions.relativeAlexanderWhitneyHomology X Y A B hA hB (p+q) z) := by
  let e := RationalSmallDescent.Constructions.binaryRationalComplementHomologyIso (TopCat.of (X×Y))
    (Prod.fst ⁻¹' A) (Prod.snd ⁻¹' B) (hA.preimage continuous_fst) (hB.preimage continuous_snd) (p+q)
  let ev := CycleClass.Geometric.RelativeChainD.Cycles.relativeHomologyEvaluation (ModuleCat.of ℚ ℚ) (TopCat.of (X×Y))
    (RelativeCrossSupport.Constructions.crossSupportComplement X Y A B) (p+q)
    (ExteriorCupSmallEvaluation.Constructions.relativeExteriorCup X Y A B hA hB p q (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ p c) (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ q d))
  let F : (SmallProductComparison.Constructions.productSmallComplementChains X Y A B).homology (p+q) ⟶ ModuleCat.of ℚ ℚ :=
    e.hom ≫ ModuleCat.ofHom ev
  let G : (SmallProductComparison.Constructions.productSmallComplementChains X Y A B).homology (p+q) ⟶ ModuleCat.of ℚ ℚ :=
    HomologicalComplex.homologyMap (SmallProductComparison.Constructions.smallRelativeAlexanderWhitney X Y A B) (p+q) ≫
      ModuleCat.ofHom (RelativeTensorHomology.Constructions.relativeTensorHomologyFunctional X Y A B p q c d)
  have hFG : F = G := by
    apply RationalizedFunctionalExt.Constructions.rationalizedHomology_functional_ext
      (CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains (TopCat.of (X×Y)) (Prod.fst ⁻¹' A) (Prod.snd ⁻¹' B)) (p+q)
    intro w
    obtain ⟨u,hu⟩ := AlgebraicTopology.Duality.Poincare.TwoSupportRelativeCap.binarySmallComplementProjection_surjective
      (TopCat.of (X×Y)) (Prod.fst ⁻¹' A) (Prod.snd ⁻¹' B) (p+q) w.val
    have huc : (CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementProjection (TopCat.of (X×Y)) (Prod.fst ⁻¹' A)
        (Prod.snd ⁻¹' B)).f (p+q) u ∈
      AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains (TopCat.of (X×Y)) (Prod.fst ⁻¹' A)
        (Prod.snd ⁻¹' B)) (p+q) := by rw [hu]; exact w.property
    have hw : (⟨(CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementProjection (TopCat.of (X×Y)) (Prod.fst ⁻¹' A)
      (Prod.snd ⁻¹' B)).f (p+q) u,huc⟩ : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles _ (p+q)) = w := Subtype.ext hu
    have h := ExteriorCupSmallEvaluation.Constructions.relativeExteriorCup_small_projection X Y A B hA hB p q c d u huc
    rw [hw] at h
    exact h
  have h := ConcreteCategory.congr_hom hFG (e.inv z)
  change ev (e.hom (e.inv z)) =
    RelativeTensorHomology.Constructions.relativeTensorHomologyFunctional X Y A B p q c d
      (HomologicalComplex.homologyMap (SmallProductComparison.Constructions.smallRelativeAlexanderWhitney X Y A B) (p+q) (e.inv z)) at h
  rw [Iso.inv_hom_id_apply] at h
  exact h

theorem relativeExteriorCup_cross_evaluation
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A p)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y B q)
    (u : CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ X A p) (v : CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ Y B q) :
    CycleClass.Geometric.RelativeChainD.Cycles.relativeHomologyEvaluation (ModuleCat.of ℚ ℚ) (TopCat.of (X×Y))
      (RelativeCrossSupport.Constructions.crossSupportComplement X Y A B) (p+q)
      (ExteriorCupSmallEvaluation.Constructions.relativeExteriorCup X Y A B hA hB p q a b)
      (RelativeCrossNonvanishing.Constructions.relativeHomologyCrossClass X Y A B p q u v) =
    CycleClass.Geometric.RelativeChainD.Cycles.relativeHomologyEvaluation (ModuleCat.of ℚ ℚ) X A p a u *
      CycleClass.Geometric.RelativeChainD.Cycles.relativeHomologyEvaluation (ModuleCat.of ℚ ℚ) Y B q b v := by
  obtain ⟨c,rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_surjective (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) p a
  obtain ⟨d,rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_surjective (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) Y B) q b
  rw [relativeExteriorCup_evaluation_whitney, RelativeTensorHomology.Constructions.relativeTensorHomologyFunctional_cross]

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExteriorCupCrossEvaluation.Constructions

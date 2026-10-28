import OAI.AlgebraicGeometry.CycleClass.Thom.Relative.Slant
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExteriorCupCrossEvaluation

/-! # Exterior Cross Degrees -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.Relative.ExteriorCrossDegrees.Constructions.Slant

/-! Integration of an actual relative exterior cup evaluates its fiber factor. -/

open _root_.CategoryTheory
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExteriorCupCrossEvaluation.Constructions

open OAI.AlgebraicGeometry.CycleClass.Thom.Relative.Slant.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Relative.CrossAssociateForward.Constructions.HomologyAssociativity

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem slant_exterior (X Y : TopCat.{0}) (A : Set X) (B : Set Y)
    (hA : IsOpen A) (hB : IsOpen B) (p q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A p)
    (d : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y B q)
    (b : Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ Y B q) :
    Slant.Constructions.slant ℚ X Y A B p q (p + q) rfl b
        (HodgeConjecture.DegreeTwo.ExteriorCupSmallEvaluation.Constructions.relativeExteriorCup X Y A B hA hB p q a d) =
      Geometric.RelativeChainD.Cycles.relativeHomologyEvaluation (ModuleCat.of ℚ ℚ) Y B q d b • a := by
  apply (Geometric.RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ X A p).injective
  ext u
  rw [Slant.Constructions.slant_evaluation, Geometric.RelativeChainD.Cycles.relativeUniversalCoefficientEquiv_apply,
    CrossAssociateForward.Constructions.HomologyAssociativity.relativeCrossClassAt_eq_original, HodgeConjecture.DegreeTwo.ExteriorCupCrossEvaluation.Constructions.relativeExteriorCup_cross_evaluation]
  simp only [map_smul, LinearMap.smul_apply,
    Geometric.RelativeChainD.Cycles.relativeUniversalCoefficientEquiv_apply, smul_eq_mul]
  exact mul_comm _ _

end AlgebraicGeometry.CycleClass.Thom.Relative.ExteriorCrossDegrees.Constructions.Slant

namespace AlgebraicGeometry.CycleClass.Thom.Relative.ExteriorCrossDegrees.Constructions

/-! An exterior cup evaluates to zero on a cross class in different factor degrees. -/

open _root_.CategoryTheory
open OAI.AlgebraicTopology.Kunneth.TensorHomologyD.Construction.TensorHomology OAI.AlgebraicTopology.Kunneth.TensorAlexanderWhitney.Construction.TensorCocycles
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExteriorCupCrossEvaluation.Constructions
open scoped TensorProduct DirectSum

open OAI.AlgebraicGeometry.CycleClass.Thom.Relative.CrossAssociateForward.Constructions.HomologyAssociativity OAI.AlgebraicGeometry.CycleClass.Thom.HomologyProductAssociativity.Constructions.Products

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem exterior_cross_other (X Y : TopCat.{0}) (A : Set X) (B : Set Y)
    (hA : IsOpen A) (hB : IsOpen B) (p q r s : ℕ) (hrs : r + s = p + q)
    (hr : r ≠ p)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A p)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y B q)
    (u : Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ X A r) (v : Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ Y B s) :
    Geometric.RelativeChainD.Cycles.relativeHomologyEvaluation (ModuleCat.of ℚ ℚ) (TopCat.of (X × Y))
      (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X Y A B) (p + q)
      (HodgeConjecture.DegreeTwo.ExteriorCupSmallEvaluation.Constructions.relativeExteriorCup X Y A B hA hB p q a b)
      (CrossAssociateForward.Constructions.HomologyAssociativity.relativeCrossClassAt ℚ X Y A B r s (p + q) hrs u v) = 0 := by
  obtain ⟨a, rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_surjective (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) p a
  obtain ⟨b, rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_surjective (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) Y B) q b
  rw [HodgeConjecture.DegreeTwo.ExteriorCupCrossEvaluation.Constructions.relativeExteriorCup_evaluation_whitney]
  have h := ConcreteCategory.congr_hom (HodgeConjecture.DegreeTwo.RelativeCrossNonvanishing.Constructions.relativeCrossWhitney_homology X Y A B hA hB (p + q))
    (AlgebraicTopology.Kunneth.TensorHomologyD.Construction.TensorHomology.algebraicKunneth (Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X A) (Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ Y B) (p + q)
      (DirectSum.lof ℚ (AlgebraicTopology.Kunneth.TensorHomologyD.Construction.TensorHomology.DegreePairs (p + q))
        (fun ij => Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ X A ij.val.1 ⊗[ℚ]
          Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ Y B ij.val.2) ⟨(r, s), hrs⟩ (u ⊗ₜ[ℚ] v)))
  change HodgeConjecture.DegreeTwo.SmallProductComparison.Constructions.relativeAlexanderWhitneyHomology X Y A B hA hB (p + q)
    (CrossAssociateForward.Constructions.HomologyAssociativity.relativeCrossClassAt ℚ X Y A B r s (p + q) hrs u v) = _ at h
  rw [h, HodgeConjecture.DegreeTwo.RelativeTensorHomology.Constructions.relativeTensorHomologyFunctional]
  apply AlgebraicTopology.Kunneth.TensorAlexanderWhitney.Construction.TensorCocycles.tensorHomologyFunctional_algebraic_other
  intro he
  exact hr (congrArg (fun ij : AlgebraicTopology.Kunneth.TensorHomologyD.Construction.TensorHomology.DegreePairs (p + q) => ij.val.1) he)

end AlgebraicGeometry.CycleClass.Thom.Relative.ExteriorCrossDegrees.Constructions

end

end OAI

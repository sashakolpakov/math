import OAI.AlgebraicTopology.Kunneth.CanonicalCohomology
import OAI.AlgebraicTopology.Cohomology.Singular.UniversalCoefficient

/-! # Homology Cross Pairing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.HomologyCrossPairing

noncomputable section

/-! Evaluate genuine degree-two singular classes on the product of two
degree-one homology classes. The product is the normalized singular
chain comparison, followed by the specified continuous multiplication. -/

open _root_.CategoryTheory OAI.AlgebraicTopology.Cohomology.Singular.UniversalCoefficient
open OAI.AlgebraicTopology.Kunneth.CanonicalCohomology.Construction.CanonicalCohomologyKunneth
open scoped TensorProduct DirectSum

variable (X : TopCat.{0})

abbrev firstHomology := (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).homology 1

def homologyCross11 : firstHomology X ⊗[ℚ] firstHomology X →ₗ[ℚ]
    (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (X × X))).homology 2 :=
  (((AlgebraicTopology.Kunneth.CanonicalCohomology.Construction.CanonicalCohomologyKunneth.productHomotopyEquiv (k := ℚ) X X).toHomologyIso 2).symm.toLinearEquiv.toLinearMap).comp
    ((AlgebraicTopology.Kunneth.TensorHomologyD.Construction.TensorHomology.algebraicKunneth (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X)
      (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X) 2).toLinearMap.comp
        (DirectSum.lof ℚ (AlgebraicTopology.Kunneth.TensorHomologyD.Construction.TensorHomology.DegreePairs 2)
          (fun ij => (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).homology ij.val.1 ⊗[ℚ]
            (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).homology ij.val.2) ⟨(1, 1), rfl⟩))

def homologyClassPairing (m : TopCat.of (X × X) ⟶ X)
    (c : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X 2) :
    firstHomology X →ₗ[ℚ] firstHomology X →ₗ[ℚ] ℚ :=
  TensorProduct.curry ((AlgebraicTopology.Cohomology.Singular.UniversalCoefficient.singularUniversalCoefficientEquiv X 2 c).comp
    ((HomologicalComplex.homologyMap ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains ℚ).map m) 2).hom.comp
      (homologyCross11 X)))

theorem homologyClassPairing_apply (m : TopCat.of (X × X) ⟶ X)
    (c : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X 2) (x y : firstHomology X) :
    homologyClassPairing X m c x y =
      AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) X 2 c
        (HomologicalComplex.homologyMap ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains ℚ).map m) 2
          (homologyCross11 X (x ⊗ₜ[ℚ] y))) := rfl

/-- The alternating part uses the two actual orientations of the
homology product, normalized by one half. -/
def alternatingClassPairing (m : TopCat.of (X × X) ⟶ X)
    (c : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X 2) :
    firstHomology X →ₗ[ℚ] firstHomology X →ₗ[ℚ] ℚ :=
  (1 / 2 : ℚ) • (homologyClassPairing X m c - (homologyClassPairing X m c).flip)

theorem alternatingClassPairing_alternating (m : TopCat.of (X × X) ⟶ X)
    (c : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X 2) (x : firstHomology X) :
    alternatingClassPairing X m c x x = 0 := by
  change (1 / 2 : ℚ) * (homologyClassPairing X m c x x - homologyClassPairing X m c x x) = 0
  rw [sub_self, mul_zero]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.HomologyCrossPairing

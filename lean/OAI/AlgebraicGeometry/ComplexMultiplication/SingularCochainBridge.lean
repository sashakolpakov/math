import OAI.AlgebraicTopology.Cohomology.Singular.InjectiveChainDual
import OAI.AlgebraicTopology.Singular.CohomologyTo

/-! # Singular Cochain Bridge -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.SingularCochainBridge

noncomputable section

/-! # The two genuine singular-cochain constructions

Evaluation on actual singular chains identifies opposite-category cochains with
the original framework's linear-dual cochains, including their pullback maps.
-/

open _root_.CategoryTheory

variable (R : Type) [CommRing R]

/-- Evaluation identifies the unchanged cochain complexes in every degree. -/
def singularCochainBridgeIso (X : TopCat.{0}) :
    AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X ≅
      AlgebraicTopology.Singular.CohomologyTo.SingularCochainComplex R X :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (AlgebraicTopology.Cohomology.Singular.ChainDual.singularDegreewiseChainDualEquiv
      (ModuleCat.of R R) X n).toModuleIso)
    (by
      intro i j _
      apply ModuleCat.hom_ext
      ext c : 1
      change (AlgebraicTopology.Cohomology.Singular.ChainDual.degreewiseChainDualEquiv
        (TopCat.toSSet.obj X) (ModuleCat.of R R) i c).comp
          ((AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).d j i).hom =
        AlgebraicTopology.Cohomology.Singular.ChainDual.degreewiseChainDualEquiv
          (TopCat.toSSet.obj X) (ModuleCat.of R R) j
          ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).d i j c)
      exact (AlgebraicTopology.Cohomology.Singular.ChainDual.degreewiseChainDualEquiv_d
        (TopCat.toSSet.obj X) (ModuleCat.of R R) i j c).symm)

/-- The comparison intertwines the actual pullback maps on cochains. -/
theorem singularCochainBridgeIso_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) :
    AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of R R) f ≫
        (singularCochainBridgeIso R X).hom =
      (singularCochainBridgeIso R Y).hom ≫ AlgebraicTopology.Singular.CohomologyTo.singularCochainComplexMap R f := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  ext c : 1
  exact AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.degreewiseChainDualEquiv_pullback
    (ModuleCat.of R R) (TopCat.toSSet.map f) n c

/-- The induced comparison on actual singular cohomology, without finiteness assumptions. -/
def singularCohomologyBridgeEquiv (X : TopCat.{0}) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of R R) X n ≃ₗ[R]
      AlgebraicTopology.Singular.CohomologyTo.Cohomology R X n :=
  ((HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℕ) n).mapIso
    (singularCochainBridgeIso R X)).toLinearEquiv

/-- Equality of the induced pullbacks on cohomology. -/
theorem singularCohomologyBridgeEquiv_naturality {X Y : TopCat.{0}}
    (f : X ⟶ Y) (n : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of R R) Y n) :
    singularCohomologyBridgeEquiv R X n
        (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of R R) f n c) =
      AlgebraicTopology.Singular.CohomologyTo.cohomologyMap R n f (singularCohomologyBridgeEquiv R Y n c) := by
  have h := congrArg (fun g => HomologicalComplex.homologyMap g n)
    (singularCochainBridgeIso_naturality R f)
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at h
  exact ConcreteCategory.congr_hom h c

end

end OAI.AlgebraicGeometry.ComplexMultiplication.SingularCochainBridge

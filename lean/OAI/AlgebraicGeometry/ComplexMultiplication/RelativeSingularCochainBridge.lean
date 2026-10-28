import OAI.AlgebraicGeometry.ComplexMultiplication.SingularCochainBridge
import OAI.AlgebraicTopology.Cohomology.Singular.RelativeSequence
import OAI.AlgebraicTopology.Singular.RelativeCochainG

/-! # Relative Singular Cochain Bridge -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.RelativeSingularCochainBridge

noncomputable section

/-! # The two actual relative singular-cochain constructions -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits OAI.AlgebraicTopology.Singular

variable (R : Type) [CommRing R]

/-- The original relative dual cochains are the kernel of actual restriction. -/
theorem originalRelativeCochainSequence_shortExact (X : TopCat.{0}) (A : Set X) :
    (AlgebraicTopology.Singular.RelativeCochainCone.relativeDualCochainShortComplexNat R (TopPair.ofSubset A)).ShortExact := by
  rw [HomologicalComplex.shortExact_iff_degreewise_shortExact]
  exact fun n => (AlgebraicTopology.Singular.RelativeCochainG.relativeDualCochainShortComplexNatDegreewiseSplitting R
    (TopPair.ofSubset A) n).shortExact

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation of actual cochains identifies the kernels of the same subspace restriction. -/
def relativeSingularCochainBridgeIso (X : TopCat.{0}) (A : Set X) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of R R) X A ≅
      AlgebraicTopology.Singular.Cohomology.RelativeCochainComplex R (TopPair.ofSubset A) :=
  KernelFork.mapIsoOfIsLimit
    (kernelIsKernel (AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction (ModuleCat.of R R) X A))
    (originalRelativeCochainSequence_shortExact R X A).fIsKernel
    (Arrow.isoMk (SingularCochainBridge.singularCochainBridgeIso R X)
      (SingularCochainBridge.singularCochainBridgeIso R (TopCat.of A))
      (by
        change (SingularCochainBridge.singularCochainBridgeIso R X).hom ≫
          AlgebraicTopology.Singular.CohomologyTo.singularCochainComplexMap R (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X A) = _
        exact (SingularCochainBridge.singularCochainBridgeIso_naturality R
          (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X A)).symm))

set_option backward.isDefEq.respectTransparency false in
/-- The relative comparison commutes with forgetting the support already on cochains. -/
theorem relativeSingularCochainBridgeIso_inclusion (X : TopCat.{0}) (A : Set X) :
    (relativeSingularCochainBridgeIso R X A).hom ≫
        (AlgebraicTopology.Singular.RelativeCochainCone.relativeDualCochainShortComplexNat R (TopPair.ofSubset A)).f =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of R R) X A ≫
        (SingularCochainBridge.singularCochainBridgeIso R X).hom := by
  dsimp only [relativeSingularCochainBridgeIso, KernelFork.mapIsoOfIsLimit]
  exact KernelFork.mapOfIsLimit_ι _ _ _

/-- The same actual comparison on relative cohomology in every degree. -/
def relativeSingularCohomologyBridgeEquiv (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of R R) X A n ≃ₗ[R]
      AlgebraicTopology.Singular.Cohomology.RelativeCohomology R (TopPair.ofSubset A) n :=
  ((HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℕ) n).mapIso
    (relativeSingularCochainBridgeIso R X A)).toLinearEquiv

end

end OAI.AlgebraicGeometry.ComplexMultiplication.RelativeSingularCochainBridge

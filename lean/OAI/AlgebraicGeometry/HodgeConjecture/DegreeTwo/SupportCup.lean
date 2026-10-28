import OAI.AlgebraicTopology.Duality.Poincare.RelativeCapHomologyNaturality
import OAI.AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeUniversalCoefficientNaturality
import OAI.AlgebraicTopology.Products.CapBoundary

/-! # Support Cup -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportCup.Constructions

noncomputable section

section

/-!
# DegreeTwo: the canonical cup product retaining both supports

The actual two-support cap pairing and the actual relative rational UCT
construct a product supported on the intersection of the two closed
supports. Its evaluation and continuous-map naturality are proved from
the original finite-chain cap construction.
-/

open _root_.CategoryTheory
open OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeUniversalCoefficientNaturality.Cycles

variable (X : TopCat.{0}) (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) (p q : ℕ)

/-- The actual relative evaluation of the cap output is a rational
bilinear functional on integral union-relative homology. -/
def twoSupportCupFunctional :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A p →ₗ[ℚ]
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X B q →ₗ[ℚ]
        (CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology X (A ∪ B) (p + q) →ₗ[ℤ] ℚ)) where
  toFun a := {
    toFun := fun b => ((CycleClass.Geometric.RelativeChainD.Cycles.relativeHomologyEvaluation (ModuleCat.of ℚ ℚ) X B q b).restrictScalars ℤ).comp
      (AlgebraicTopology.Duality.Poincare.SupportRelativeCapHomology.twoSupportRelativeCapHomology X A B hA hB p q a)
    map_add' := by
      intro b c
      ext z
      exact LinearMap.congr_fun (map_add (CycleClass.Geometric.RelativeChainD.Cycles.relativeHomologyEvaluation (ModuleCat.of ℚ ℚ) X B q) b c) _
    map_smul' := by
      intro r b
      ext z
      exact LinearMap.congr_fun (map_smul (CycleClass.Geometric.RelativeChainD.Cycles.relativeHomologyEvaluation (ModuleCat.of ℚ ℚ) X B q) r b) _ }
  map_add' a c := by
    ext b z
    change CycleClass.Geometric.RelativeChainD.Cycles.relativeHomologyEvaluation (ModuleCat.of ℚ ℚ) X B q b
      (AlgebraicTopology.Duality.Poincare.SupportRelativeCapHomology.twoSupportRelativeCapHomology X A B hA hB p q (a + c) z) = _
    rw [map_add, LinearMap.add_apply, map_add]
    rfl
  map_smul' r a := by
    ext b z
    change CycleClass.Geometric.RelativeChainD.Cycles.relativeHomologyEvaluation (ModuleCat.of ℚ ℚ) X B q b
      (AlgebraicTopology.Duality.Poincare.SupportRelativeCapHomology.twoSupportRelativeCapHomology X A B hA hB p q (r • a) z) = _
    rw [map_smul, LinearMap.smul_apply, map_smul]
    rfl

/-- The UCT realizes this actual cap functional in relative cohomology
of the union complement, hence with the intersection support retained. -/
def twoSupportCohomologyCup :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A p →ₗ[ℚ]
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X B q →ₗ[ℚ]
        AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X (A ∪ B) (p + q)) where
  toFun a := (AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.relativeRationalUniversalCoefficientEquiv X (A ∪ B) (p + q)).symm.toLinearMap.comp
    (twoSupportCupFunctional X A B hA hB p q a)
  map_add' a c := by
    ext b
    simp only [LinearMap.comp_apply, map_add, LinearMap.add_apply]
  map_smul' r a := by
    ext b
    simp only [LinearMap.comp_apply, map_smul, LinearMap.smul_apply, RingHom.id_apply]

/-- Literal cap/cup adjunction on the original relative homology. -/
theorem twoSupportCohomologyCup_evaluation
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A p)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X B q)
    (z : CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology X (A ∪ B) (p + q)) :
    AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.relativeRationalHomologyEvaluation X (A ∪ B) (p + q)
        (twoSupportCohomologyCup X A B hA hB p q a b) z =
      CycleClass.Geometric.RelativeChainD.Cycles.relativeHomologyEvaluation (ModuleCat.of ℚ ℚ) X B q b
        (AlgebraicTopology.Duality.Poincare.SupportRelativeCapHomology.twoSupportRelativeCapHomology X A B hA hB p q a z) := by
  exact LinearMap.congr_fun
    ((AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.relativeRationalUniversalCoefficientEquiv X (A ∪ B) (p + q)).apply_symm_apply
      (twoSupportCupFunctional X A B hA hB p q a b)) z

/-- The product is natural under the actual continuous maps of both
pairs, with the actual union-relative map on its output. -/
theorem twoSupportCohomologyCup_naturality
    {Y : TopCat.{0}} (f : X ⟶ Y) (A' B' : Set Y) (hA' : IsOpen A') (hB' : IsOpen B')
    (hfA : Set.MapsTo f A A') (hfB : Set.MapsTo f B B')
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y A' p)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y B' q) :
    twoSupportCohomologyCup X A B hA hB p q
        (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f hfA p a)
        (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f hfB q b) =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f (hfA.union_union hfB) (p + q)
        (twoSupportCohomologyCup Y A' B' hA' hB' p q a b) := by
  apply (AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.relativeRationalUniversalCoefficientEquiv X (A ∪ B) (p + q)).injective
  apply LinearMap.ext
  intro z
  change AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.relativeRationalHomologyEvaluation X (A ∪ B) (p + q) _ z =
    AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.relativeRationalHomologyEvaluation X (A ∪ B) (p + q) _ z
  rw [twoSupportCohomologyCup_evaluation, AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.relativeRationalHomologyEvaluation_naturality,
    twoSupportCohomologyCup_evaluation, CycleClass.Geometric.RelativeUniversalCoefficientNaturality.Cycles.relativeHomologyEvaluation_naturality,
    AlgebraicTopology.Duality.Poincare.RelativeCapHomologyNaturality.twoSupportRelativeCapHomology_naturality f hfA hfB hA hB hA' hB']

end

/-!
# DegreeTwo: the supported cup evaluated on actual chain representatives

An ambient chain need only become a cycle in the binary-small quotient.
On that represented relative class, the two-support cup is evaluated by
the original finite Alexander–Whitney cup formula.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeUniversalCoefficientNaturality.Cycles OAI.AlgebraicTopology.Products.CapBoundary

set_option backward.isDefEq.respectTransparency false

variable (X : TopCat.{0}) (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) (p q : ℕ)
variable (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) p)
variable (d : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X B) q)
variable (z : (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X (p + q))
variable (hz : (CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementProjection X A B).f (p + q) z ∈
  AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B) (p + q))

theorem twoSupportCup_small_projection_cap :
    AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.relativeRationalHomologyEvaluation X (A ∪ B) (p + q)
      (twoSupportCohomologyCup X A B hA hB p q
        (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ p c) (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ q d))
      ((CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementHomologyIso X A B hA hB (p + q)).hom
        (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass _ (p + q) ⟨(CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementProjection X A B).f (p + q) z,hz⟩)) =
    AlgebraicTopology.Cohomology.Singular.ChainDual.singularDegreewiseChainDualEquiv (ModuleCat.of ℚ ℚ) X q
      ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X B).f q d.val)
      (AlgebraicTopology.Duality.Poincare.IntegralCapCoefficients.mixedSingularCap X p q ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f p c.val) z) := by
  rw [twoSupportCohomologyCup_evaluation, AlgebraicTopology.Duality.Poincare.SupportRelativeCapHomology.twoSupportRelativeCapHomology_class_class,
    CycleClass.Geometric.RelativeChainD.Cycles.relativeHomologyEvaluation_class_class]
  change CycleClass.Geometric.RelativeChainD.Cycles.relativeDegreewiseChainDualEquiv (ModuleCat.of ℚ ℚ) X B q d.val
    (AlgebraicTopology.Duality.Poincare.TwoSupportRelativeCap.twoSupportSmallCap X A B p q c.val ((CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementProjection X A B).f (p+q) z)) = _
  rw [AlgebraicTopology.Duality.Poincare.TwoSupportRelativeCap.twoSupportSmallCap_projection, CycleClass.Geometric.RelativeChainD.Cycles.relativeDegreewiseChainDualEquiv_projection]

theorem twoSupportCup_small_projection_cup :
    AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.relativeRationalHomologyEvaluation X (A ∪ B) (p + q)
      (twoSupportCohomologyCup X A B hA hB p q
        (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ p c) (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ q d))
      ((CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementHomologyIso X A B hA hB (p + q)).hom
        (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass _ (p + q) ⟨(CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementProjection X A B).f (p + q) z,hz⟩)) =
    AlgebraicTopology.Cohomology.Singular.ChainDual.singularDegreewiseChainDualEquiv (ModuleCat.of ℚ ℚ) X (p + q)
      (AlgebraicTopology.Products.Cup.singularCup X ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f p c.val)
        ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X B).f q d.val))
      (AlgebraicTopology.Duality.Poincare.IntegralCapCoefficients.integralToScalarSingular (R := ℚ) X (p + q) z) := by
  rw [twoSupportCup_small_projection_cap, AlgebraicTopology.Duality.Poincare.IntegralCapCoefficients.mixedSingularCap_apply]
  have hmul : LinearMap.lsmul ℚ ℚ = LinearMap.mul ℚ ℚ := rfl
  have h := AlgebraicTopology.Products.CapBoundary.cap_cupWith_pairing (TopCat.toSSet.obj X) (ModuleCat.of ℚ ℚ)
    ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f p c.val)
    ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X B).f q d.val)
    (AlgebraicTopology.Duality.Poincare.IntegralCapCoefficients.integralToScalarSingular (R := ℚ) X (p + q) z)
  rw [hmul] at h
  exact h.symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportCup.Constructions

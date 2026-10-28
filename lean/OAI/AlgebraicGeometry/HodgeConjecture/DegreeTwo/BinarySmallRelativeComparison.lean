import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.BinarySmallCochains
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeUniversalCoefficientNaturality

/-! # Binary Small Relative Comparison -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.BinarySmallRelativeComparison.Constructions

noncomputable section

/-! The native relative-cochain comparison, retaining rational scalars and evaluation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeUniversalCoefficientNaturality.Cycles

set_option backward.isDefEq.respectTransparency false

variable (X : TopCat.{0}) (A B : Set X)

def binarySmallRelativeCochainMap :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (A ∪ B) ⟶ BinarySmallCochains.Constructions.binarySmallCochains X A B where
  f n := ModuleCat.ofHom {
    toFun := fun c => (AlgebraicTopology.Duality.Poincare.RelativeCochainDual.relativeCochainIntegralDualEquiv X (A ∪ B) n c).comp
      ((CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementToRelative X A B).f n).hom
    map_add' := by intros; simp only [map_add, LinearMap.add_comp]
    map_smul' := by intros; simp only [map_smul, LinearMap.smul_comp, RingHom.id_apply] }
  comm' i j _ := by
    ext c z
    change AlgebraicTopology.Duality.Poincare.RelativeCochainDual.relativeCochainIntegralDualEquiv X (A ∪ B) i c
      ((CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementToRelative X A B).f i
        ((CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B).d j i z)) =
      AlgebraicTopology.Duality.Poincare.RelativeCochainDual.relativeCochainIntegralDualEquiv X (A ∪ B) j
        ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (A ∪ B)).d i j c)
        ((CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementToRelative X A B).f j z)
    rw [AlgebraicTopology.Duality.Poincare.RelativeCochainDual.relativeCochainIntegralDualEquiv_d]
    exact congrArg (AlgebraicTopology.Duality.Poincare.RelativeCochainDual.relativeCochainIntegralDualEquiv X (A ∪ B) i c)
      (ConcreteCategory.congr_hom ((CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementToRelative X A B).comm j i) z).symm

theorem binarySmallRelativeCochainMap_inclusion (n : ℕ)
    (c : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (A ∪ B)).X n) :
    BinarySmallCochains.Constructions.binarySmallCochainInclusion X A B n ((binarySmallRelativeCochainMap X A B).f n c) =
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X (A ∪ B)).f n c := by
  apply (BinarySmallCochains.Constructions.rationalSingularIntegralDualEquiv X n).injective
  ext z
  rw [BinarySmallCochains.Constructions.binarySmallCochainInclusion_eval]
  change AlgebraicTopology.Duality.Poincare.RelativeCochainDual.relativeCochainIntegralDualEquiv X (A ∪ B) n c
    ((CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementToRelative X A B).f n
      ((CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementProjection X A B).f n z)) = _
  rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f,
    CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementToRelative_projection]
  exact AlgebraicTopology.Duality.Poincare.RelativeCochainDual.relativeCochainIntegralDualEquiv_projection X (A ∪ B) n c z

theorem binarySmallRelativeCohomologyMap_evaluation (n : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X (A ∪ B) n)
    (z : (CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B).homology n) :
    RationalDualComplex.Constructions.integralRationalDualUniversalCoefficientEquiv (CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B) n
      (HomologicalComplex.homologyMap (binarySmallRelativeCochainMap X A B) n a) z =
    AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.relativeRationalHomologyEvaluation X (A ∪ B) n a
      (HomologicalComplex.homologyMap (CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementToRelative X A B) n z) := by
  obtain ⟨c,rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_surjective
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (A ∪ B)) n a
  obtain ⟨w,rfl⟩ := AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass_surjective (CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B) n z
  rw [AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality, RationalDualComplex.Constructions.integralRationalDualUniversalCoefficientEquiv_class_class,
    AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainClass_naturality, AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.relativeRationalHomologyEvaluation_class_class]
  rfl

theorem binarySmallRelativeCohomologyMap_bijective (hA : IsOpen A) (hB : IsOpen B) (n : ℕ) :
    Function.Bijective (HomologicalComplex.homologyMap (binarySmallRelativeCochainMap X A B) n) := by
  let H := CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementHomologyIso X A B hA hB n
  constructor
  · intro a b hab
    apply (AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.relativeRationalUniversalCoefficientEquiv X (A ∪ B) n).injective
    ext z
    rw [AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.relativeRationalUniversalCoefficientEquiv_apply,
      AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.relativeRationalUniversalCoefficientEquiv_apply]
    have h := congrArg (fun c => RationalDualComplex.Constructions.integralRationalDualUniversalCoefficientEquiv
      (CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B) n c (H.inv z)) hab
    rw [binarySmallRelativeCohomologyMap_evaluation,
      binarySmallRelativeCohomologyMap_evaluation] at h
    change AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.relativeRationalHomologyEvaluation X (A ∪ B) n a (H.hom (H.inv z)) =
      AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.relativeRationalHomologyEvaluation X (A ∪ B) n b (H.hom (H.inv z)) at h
    simpa only [Iso.inv_hom_id_apply] using h
  · intro b
    let φ := (RationalDualComplex.Constructions.integralRationalDualUniversalCoefficientEquiv
      (CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B) n b).comp H.inv.hom
    refine ⟨(AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.relativeRationalUniversalCoefficientEquiv X (A ∪ B) n).symm φ, ?_⟩
    apply (RationalDualComplex.Constructions.integralRationalDualUniversalCoefficientEquiv
      (CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B) n).injective
    ext z
    rw [binarySmallRelativeCohomologyMap_evaluation]
    change (AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.relativeRationalUniversalCoefficientEquiv X (A ∪ B) n)
      ((AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.relativeRationalUniversalCoefficientEquiv X (A ∪ B) n).symm φ) (H.hom z) = _
    rw [LinearEquiv.apply_symm_apply]
    change RationalDualComplex.Constructions.integralRationalDualUniversalCoefficientEquiv
      (CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B) n b (H.inv (H.hom z)) = _
    rw [Iso.hom_inv_id_apply]

def binarySmallRelativeCohomologyIso (hA : IsOpen A) (hB : IsOpen B) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X (A ∪ B) n ≅
      (BinarySmallCochains.Constructions.binarySmallCochains X A B).homology n :=
  (LinearEquiv.ofBijective
    (HomologicalComplex.homologyMap (binarySmallRelativeCochainMap X A B) n).hom
    (binarySmallRelativeCohomologyMap_bijective X A B hA hB n)).toModuleIso

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.BinarySmallRelativeComparison.Constructions

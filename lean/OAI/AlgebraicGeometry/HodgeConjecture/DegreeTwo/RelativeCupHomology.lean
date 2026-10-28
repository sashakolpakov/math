import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.GoodShiftRepresentatives
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalOrdinaryThomIso

/-! # Relative Cup Homology -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCupHomology.Constructions

noncomputable section

/-! The shifted cochain cup induces the original relative cup on categorical cohomology. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false

variable (X : TopCat.{0}) (C : Set X)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X C) 2)

theorem relativeTwoCupGoodShiftHomology_eq (q : ℕ) :
    HomologicalComplex.homologyMap (RelativeCupHomotopy.Constructions.relativeTwoCupGoodShiftMap X C a) q ≫
        (GoodShiftCohomology.Constructions.cochainGoodShiftHomologyIso (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X C) 2 q).hom =
      ModuleCat.ofHom (CycleClass.Geometric.RelativeCupCohomology.Cycles.relativeAbsoluteCohomologyCup (R := ℚ) X C 2 q
        (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X C) 2 a)) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro b
  obtain ⟨b,rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_surjective (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X) q b
  rw [ConcreteCategory.comp_apply, AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality]
  change (GoodShiftCohomology.Constructions.cochainGoodShiftHomologyIso (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X C) 2 q).hom
    (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ q (GoodShiftRepresentatives.Constructions.cochainGoodShiftCocycle
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X C) 2 q
      (CycleClass.Geometric.RelativeCupCohomology.Cycles.relativeAbsoluteCocycleCupWith X C
        (M := ModuleCat.of ℚ ℚ) (N := ModuleCat.of ℚ ℚ) (L := ModuleCat.of ℚ ℚ)
        (LinearMap.mul ℚ ℚ) 2 q a b))) = _
  rw [GoodShiftRepresentatives.Constructions.cochainGoodShiftHomologyIso_class]
  exact (CycleClass.Geometric.RelativeCupCohomology.Cycles.relativeAbsoluteCohomologyCup_class_class X C a b).symm

theorem relativeTwoCupGoodShift_quasiIso_of_cup_bijective
    (ha : ∀ q, Function.Bijective (CycleClass.Geometric.RelativeCupCohomology.Cycles.relativeAbsoluteCohomologyCup (R := ℚ) X C 2 q
      (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X C) 2 a))) :
    QuasiIso (RelativeCupHomotopy.Constructions.relativeTwoCupGoodShiftMap X C a) := by
  rw [quasiIso_iff]
  intro q
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have : IsIso (HomologicalComplex.homologyMap (RelativeCupHomotopy.Constructions.relativeTwoCupGoodShiftMap X C a) q ≫
      (GoodShiftCohomology.Constructions.cochainGoodShiftHomologyIso (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X C) 2 q).hom) := by
    rw [relativeTwoCupGoodShiftHomology_eq, ConcreteCategory.isIso_iff_bijective]
    exact ha q
  exact IsIso.of_isIso_comp_right _
    (GoodShiftCohomology.Constructions.cochainGoodShiftHomologyIso (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X C) 2 q).hom

variable {M N : Type} [TopologicalSpace M] [TopologicalSpace N] {d : ℕ}
variable {f : M → N} {x : M}
variable (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair (Fin d → ℂ) (Fin 1 → ℂ) f x) (hf : Topology.IsEmbedding f)

include hf

theorem normalPairRelativeTwoCupGoodShift_quasiIso
    (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
      (TopCat.of P.neighborhood) P.relativeComplement) 2)
    (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
      (TopCat.of P.neighborhood) P.relativeComplement) 2 a = P.rationalClassFin) :
    QuasiIso (RelativeCupHomotopy.Constructions.relativeTwoCupGoodShiftMap (TopCat.of P.neighborhood) P.relativeComplement a) := by
  apply relativeTwoCupGoodShift_quasiIso_of_cup_bijective
  intro q
  rw [ha]
  have h : CycleClass.Geometric.RelativeCupCohomology.Cycles.relativeAbsoluteCohomologyCup (R := ℚ) (TopCat.of P.neighborhood)
      P.relativeComplement 2 q P.rationalClassFin = (NormalOrdinaryThomIso.Constructions.normalPairOrdinaryThomIso P hf q).toLinearMap := by
    apply LinearMap.ext
    intro b
    exact (NormalOrdinaryThomIso.Constructions.normalPairOrdinaryThomIso_eq_cup P hf q b).symm
  rw [h]
  exact (NormalOrdinaryThomIso.Constructions.normalPairOrdinaryThomIso P hf q).bijective

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCupHomology.Constructions

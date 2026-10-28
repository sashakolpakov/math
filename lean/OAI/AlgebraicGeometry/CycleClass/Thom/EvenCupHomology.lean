import OAI.AlgebraicGeometry.CycleClass.Thom.EvenCupComplex
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.GoodShiftRepresentatives
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalOrdinaryThomIso

/-! # Even Cup Homology -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.EvenCupHomology.Constructions

noncomputable section

/-! The shifted cochain cup induces the original relative cup on categorical cohomology. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false

variable (X : TopCat.{0}) (C : Set X)
variable {p : ℕ}
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X C) (2 * p))

theorem relativeEvenCupGoodShiftHomology_eq (q : ℕ) :
    HomologicalComplex.homologyMap (EvenCupComplex.Constructions.relativeEvenCupGoodShiftMap X C a) q ≫
        (HodgeConjecture.DegreeTwo.GoodShiftCohomology.Constructions.cochainGoodShiftHomologyIso (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X C) (2 * p) q).hom =
      ModuleCat.ofHom (Geometric.RelativeCupCohomology.Cycles.relativeAbsoluteCohomologyCup (R := ℚ) X C (2 * p) q
        (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X C) (2 * p) a)) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro b
  obtain ⟨b,rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_surjective (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X) q b
  rw [ConcreteCategory.comp_apply, AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality]
  change (HodgeConjecture.DegreeTwo.GoodShiftCohomology.Constructions.cochainGoodShiftHomologyIso (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X C) (2 * p) q).hom
    (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ q (HodgeConjecture.DegreeTwo.GoodShiftRepresentatives.Constructions.cochainGoodShiftCocycle
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X C) (2 * p) q
      (Geometric.RelativeCupCohomology.Cycles.relativeAbsoluteCocycleCupWith X C
        (M := ModuleCat.of ℚ ℚ) (N := ModuleCat.of ℚ ℚ) (L := ModuleCat.of ℚ ℚ)
        (LinearMap.mul ℚ ℚ) (2 * p) q a b))) = _
  rw [HodgeConjecture.DegreeTwo.GoodShiftRepresentatives.Constructions.cochainGoodShiftHomologyIso_class]
  exact (Geometric.RelativeCupCohomology.Cycles.relativeAbsoluteCohomologyCup_class_class X C a b).symm

theorem relativeEvenCupGoodShift_quasiIso_of_cup_bijective
    (ha : ∀ q, Function.Bijective (Geometric.RelativeCupCohomology.Cycles.relativeAbsoluteCohomologyCup (R := ℚ) X C (2 * p) q
      (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X C) (2 * p) a))) :
    QuasiIso (EvenCupComplex.Constructions.relativeEvenCupGoodShiftMap X C a) := by
  rw [quasiIso_iff]
  intro q
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have : IsIso (HomologicalComplex.homologyMap (EvenCupComplex.Constructions.relativeEvenCupGoodShiftMap X C a) q ≫
      (HodgeConjecture.DegreeTwo.GoodShiftCohomology.Constructions.cochainGoodShiftHomologyIso (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X C) (2 * p) q).hom) := by
    rw [relativeEvenCupGoodShiftHomology_eq, ConcreteCategory.isIso_iff_bijective]
    exact ha q
  exact IsIso.of_isIso_comp_right _
    (HodgeConjecture.DegreeTwo.GoodShiftCohomology.Constructions.cochainGoodShiftHomologyIso (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X C) (2 * p) q).hom

variable {M N : Type} [TopologicalSpace M] [TopologicalSpace N] {d : ℕ}
variable {f : M → N} {x : M}
variable (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair (Fin d → ℂ) (Fin p → ℂ) f x) (hf : Topology.IsEmbedding f)

include hf

theorem normalPairRelativeEvenCupGoodShift_quasiIso
    (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
      (TopCat.of P.neighborhood) P.relativeComplement) (2 * p))
    (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
      (TopCat.of P.neighborhood) P.relativeComplement) (2 * p) a = P.rationalClassFin) :
    QuasiIso (EvenCupComplex.Constructions.relativeEvenCupGoodShiftMap (TopCat.of P.neighborhood) P.relativeComplement a) := by
  apply relativeEvenCupGoodShift_quasiIso_of_cup_bijective
  intro q
  rw [ha]
  have h : Geometric.RelativeCupCohomology.Cycles.relativeAbsoluteCohomologyCup (R := ℚ) (TopCat.of P.neighborhood)
      P.relativeComplement (2 * p) q P.rationalClassFin = (HodgeConjecture.DegreeTwo.NormalOrdinaryThomIso.Constructions.normalPairOrdinaryThomIso P hf q).toLinearMap := by
    apply LinearMap.ext
    intro b
    exact (HodgeConjecture.DegreeTwo.NormalOrdinaryThomIso.Constructions.normalPairOrdinaryThomIso_eq_cup P hf q b).symm
  rw [h]
  exact (HodgeConjecture.DegreeTwo.NormalOrdinaryThomIso.Constructions.normalPairOrdinaryThomIso P hf q).bijective

end

end OAI.AlgebraicGeometry.CycleClass.Thom.EvenCupHomology.Constructions

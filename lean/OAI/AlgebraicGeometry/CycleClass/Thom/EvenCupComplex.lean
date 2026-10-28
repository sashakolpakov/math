import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCupHomotopy

/-! # Even Cup Complex -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.EvenCupComplex

noncomputable section

/-! Cup with any actual relative cocycle of even degree defines the
corresponding shifted cochain map. -/

open _root_.CategoryTheory
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCupHomotopy.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Constructions

variable (X : TopCat.{0}) (C : Set X) {p : ℕ}
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X C) (2 * p))

theorem relativeDegreeEvenCup_d (q : ℕ) (b : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).X q) :
    (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).d (2 * p + q) (2 * p + q + 1)
      (AlgebraicTopology.Products.Cup.singularCup X ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X C).f (2 * p) a.val) b) =
    AlgebraicTopology.Products.Cup.singularCup X ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X C).f (2 * p) a.val)
      ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).d q (q + 1) b) := by
  have ha : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).d (2 * p) (2 * p + 1)
      ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X C).f (2 * p) a.val) = 0 :=
    AlgebraicTopology.Cohomology.Singular.Evaluation.cochainCocycle_d_eq_zero _ (2 * p) (2 * p + 1)
      (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X C) (2 * p) a)
  change (AlgebraicTopology.Cohomology.Singular.Basic.simplicialCochains (TopCat.toSSet.obj X) (ModuleCat.of ℚ ℚ)).d (2 * p + q) (2 * p + q + 1)
    (AlgebraicTopology.Products.Cup.cupWith (TopCat.toSSet.obj X) (LinearMap.mul ℚ ℚ)
      ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X C).f (2 * p) a.val) b) = _
  rw [AlgebraicTopology.Products.Cup.cupWith_coboundary, ha, AlgebraicTopology.Products.Cup.cupWith_zero_left, map_zero, zero_add]
  simp only [pow_mul, neg_one_sq, one_pow, one_smul]
  rfl

def relativeEvenCupCochainMap :
    AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X ⟶
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X C).restriction (HodgeConjecture.DegreeTwo.RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding (2 * p)) where
  f n := ModuleCat.ofHom (Geometric.RelativeCup.Cycles.relativeAbsoluteCup X C (2 * p) n a.val)
  comm' i j hij := by
    have hj : i + 1 = j := hij
    subst j
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro b
    change (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X C).d (2 * p + i) (2 * p + (i + 1))
        (Geometric.RelativeCup.Cycles.relativeAbsoluteCup X C (2 * p) i a.val b) =
      Geometric.RelativeCup.Cycles.relativeAbsoluteCup X C (2 * p) (i + 1) a.val ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).d i (i + 1) b)
    apply Geometric.RelativeCochainHomotopy.Cohomology.relativeCochainInclusion_injective (ModuleCat.of ℚ ℚ) X C (2 * p + (i + 1))
    rw [HodgeConjecture.DegreeTwo.SupportCupDifferential.Constructions.relativeCochainInclusion_d_apply]
    simp only [Geometric.RelativeCup.Cycles.relativeAbsoluteCup, Geometric.RelativeCup.Cycles.relativeAbsoluteCupWith_inclusion]
    exact relativeDegreeEvenCup_d X C a i b

def relativeEvenCupGoodShiftMap :
    AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X ⟶
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X C).truncGE' (HodgeConjecture.DegreeTwo.RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding (2 * p)) :=
  relativeEvenCupCochainMap X C a ≫
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X C).restrictionToTruncGE' (HodgeConjecture.DegreeTwo.RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding (2 * p))

theorem relativeEvenCupCochainMap_naturality {Y : TopCat.{0}} (f : Y ⟶ X)
    (D : Set Y) (hf : Set.MapsTo f D C) :
    AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ) f ≫
      relativeEvenCupCochainMap Y D
        (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap (ModuleCat.of ℚ ℚ) f hf) (2 * p) a) =
    relativeEvenCupCochainMap X C a ≫
      HomologicalComplex.restrictionMap (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap (ModuleCat.of ℚ ℚ) f hf)
        (HodgeConjecture.DegreeTwo.RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding (2 * p)) := by
  ext n : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro b
  change Geometric.RelativeCup.Cycles.relativeAbsoluteCup Y D (2 * p) n
      ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap (ModuleCat.of ℚ ℚ) f hf).f (2 * p) a.val)
      ((AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ) f).f n b) =
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap (ModuleCat.of ℚ ℚ) f hf).f (2 * p + n)
      (Geometric.RelativeCup.Cycles.relativeAbsoluteCup X C (2 * p) n a.val b)
  exact (Geometric.RelativeCup.Cycles.relativeAbsoluteCupWith_pullback Y D
    (M := ModuleCat.of ℚ ℚ) (N := ModuleCat.of ℚ ℚ) (L := ModuleCat.of ℚ ℚ)
    (LinearMap.mul ℚ ℚ) f hf a.val b).symm

end Constructions

end

end OAI.AlgebraicGeometry.CycleClass.Thom.EvenCupComplex

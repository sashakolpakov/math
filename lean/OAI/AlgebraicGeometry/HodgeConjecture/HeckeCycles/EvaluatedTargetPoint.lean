import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.PELSource

/-! # Evaluated Target Point -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluatedTargetPoint.CM

noncomputable section

/-! Each NeighborCounting evaluated target is a point of the original TateComparison generic
moduli scheme over the same evaluation field. The arithmetic base is
proved from the two scalar towers and the original Witt base map; the
full target PEL family is identified by canonical pullback isomorphisms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActionFamilyComparison.Family
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM.Generic

variable {E K : Type} [Field E] [NumberField E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  (M : PELModuli.CMPoints.Models.RankThreePELModel E K) (hM : M.HasPrescribedBallPeriods)
  {q : ℕ} [Fact q.Prime] (j : M.QadicChoice q)
  (hsplit : j.HasSplitCoordinates M.extendedEmbedding)
  (R : M.GoodIntegralReduction q j)
  (labels : (Fin M.s × Bool) ≃ Gal(E/ℚ))
  (hlabels : ∀ (v : Fin M.s) (b : Bool),
    labels (v, !b) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels (v, b))
  (a : M.Family) (hden : Nat.Coprime q M.arithmetic.denominator)

  {L : Type} [Field L] [Algebra (Witt.ArithmeticBase.CM.Generic.F q) L]
  [Algebra (Witt.ArithmeticBase.CM.W (q := q)) L] [IsScalarTower (Witt.ArithmeticBase.CM.W (q := q)) (Witt.ArithmeticBase.CM.Generic.F q) L]
  (V : Isogenies.NeighborCounting.EvaluationDVRLifts.EvaluationDVR (Witt.ArithmeticBase.CM.W (q := q)) L)
  (z : Isogenies.NeighborCounting.Evaluated.Targets.Lifts.EvaluatedTarget (FrobeniusKernelLifts.CM.reduction M hM j hsplit R labels hlabels a) V.carrier L
    ((algebraMap (Witt.ArithmeticBase.CM.W (q := q)) V.carrier).comp (Witt.ArithmeticBase.CM.arithmeticMap (j := j) hden)))

theorem arithmetic_base : z.map ≫ (M.integral a).toOver.hom =
    EvaluationGenericTest.CM.originalBase (L := L) j ≫ M.arithmetic.generic := by
  refine z.overBase.trans ?_
  have hV : Spec.map (CommRingCat.ofHom (algebraMap V.carrier L)) ≫
      Isogenies.NeighborCounting.Lifts.dvrBase V.carrier
        ((algebraMap (Witt.ArithmeticBase.CM.W (q := q)) V.carrier).comp (Witt.ArithmeticBase.CM.arithmeticMap (j := j) hden)) =
      Spec.map (CommRingCat.ofHom (algebraMap (Witt.ArithmeticBase.CM.W (q := q)) L)) ≫ Witt.ArithmeticBase.CM.wittBase (j := j) hden := by
    change Spec.map (CommRingCat.ofHom (algebraMap V.carrier L)) ≫
      Spec.map (CommRingCat.ofHom _) = Spec.map (CommRingCat.ofHom _) ≫ Spec.map (CommRingCat.ofHom _)
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    ext t
    exact (IsScalarTower.algebraMap_apply (Witt.ArithmeticBase.CM.W (q := q)) V.carrier L (Witt.ArithmeticBase.CM.arithmeticMap (j := j) hden t)).symm
  rw [hV]
  have hF : Spec.map (CommRingCat.ofHom (algebraMap (Witt.ArithmeticBase.CM.W (q := q)) L)) =
      Spec.map (CommRingCat.ofHom (algebraMap (Witt.ArithmeticBase.CM.Generic.F q) L)) ≫ Witt.ArithmeticBase.CM.Generic.fractionBase (q := q) := by
    rw [Witt.ArithmeticBase.CM.Generic.fractionBase, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact RingHom.ext (IsScalarTower.algebraMap_apply (Witt.ArithmeticBase.CM.W (q := q)) (Witt.ArithmeticBase.CM.Generic.F q) L)
  rw [hF, Category.assoc, Witt.ArithmeticBase.CM.Generic.generic_square j hden, ← Category.assoc]
  rfl

def point : Over.mk (EvaluationGenericTest.CM.originalBase (L := L) j) ⟶
    (Over.pullback M.arithmetic.generic).obj (M.integral a).toOver :=
  Over.homMk (pullback.lift z.map (EvaluationGenericTest.CM.originalBase (L := L) j)
    (arithmetic_base M hM j hsplit R labels hlabels a hden V z)) (pullback.lift_snd _ _ _)

theorem point_projection :
    (point M hM j hsplit R labels hlabels a hden V z).left ≫
      pullback.fst (M.integral a).toOver.hom M.arithmetic.generic = z.map :=
  pullback.lift_fst _ _ _

variable (C : AbelianScheme.TateComparison.Local.IntegralType M.s → AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence ((Over.pullback M.arithmetic.generic).obj (M.integral a).toOver))
  (χ : Fin M.s × Bool → NumberField.RingOfIntegers E →+* ℤ_[q])

def familyIso : AbelianScheme.TateComparison.PELModuli.PELFamilyIso (Isogenies.NeighborCounting.ActionFamilyComparison.Family.actionFamily ((M.integral a).universal.data.pullback z.map))
    ((Witt.PELSource.CM.heckeData M a C χ).fiberFamily (EvaluationGenericTest.CM.originalBase (L := L) j)
      (point M hM j hsplit R labels hlabels a hden V z)) :=
  (Isogenies.NeighborCounting.ActionFamilyComparison.Family.actionFamilyPullbackIso (M.integral a).universal.data z.map).symm.trans
    ((Isogenies.NeighborCounting.ActionFamilyComparison.Family.actionFamily (M.integral a).universal.data).pullbackFactor
      (point M hM j hsplit R labels hlabels a hden V z).left
      (pullback.fst (M.integral a).toOver.hom M.arithmetic.generic) z.map
      (point_projection M hM j hsplit R labels hlabels a hden V z))

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluatedTargetPoint.CM

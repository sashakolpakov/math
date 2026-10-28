import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.PELSource

/-! # Source Extension -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.SourceExtension.CM

noncomputable section

/-! The source-family comparison persists under every further field
extension. Its arithmetic triangle follows from the actual extended
point, without choosing a new source lift or changing the PEL data. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ReductionSpecification
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.PointExt.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReductionPoints.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM.Generic
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FieldPointDescent.CM

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
  (p : Geometric.PointExt.CM.pointBase (AlgebraicClosure (ZMod q)) ⟶ R.geometricFiber a)
  (l : Isogenies.NeighborCounting.Lifts.IntegralLift (FrobeniusKernelLifts.CM.reduction M hM j hsplit R labels hlabels a)
    (ArithmeticBase.CM.W (q := q)) (ArithmeticBase.CM.arithmeticMap (j := j) hden) (ArithmeticBase.CM.residueIso (q := q)) (ReductionPoints.CM.primeFieldPoint R a p))
  {L : Type} [Field L] [Algebra (ArithmeticBase.CM.Generic.F q) L]
  (C : AbelianScheme.TateComparison.Local.IntegralType M.s → AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence ((Over.pullback M.arithmetic.generic).obj (M.integral a).toOver))
  (χ : Fin M.s × Bool → NumberField.RingOfIntegers E →+* ℤ_[q])

variable {L' : Type} [Field L'] (σ : L →+* L')

local notation "sl" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.LiftRecovery.CM.schemeLift M hM j hsplit R labels hlabels a hden p l
local notation "z" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.FieldPoint.CM.fieldPoint (L := L) (OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.Has.IntegralPELSpread.toOver (M.integral a)) sl

def point : Over.mk (Spec.map (CommRingCat.ofHom σ) ≫ EvaluationGenericTest.CM.originalBase (L := L) j) ⟶
    (PELSource.CM.heckeData M a C χ).space :=
  FieldPointDescent.CM.testMap σ (EvaluationGenericTest.CM.originalBase (L := L) j) ≫ z

theorem point_projection :
    (point M hM j hsplit R labels hlabels a hden p l C χ σ).left ≫
      pullback.fst (M.integral a).toOver.hom M.arithmetic.generic =
    (Spec.map (CommRingCat.ofHom σ) ≫ Spec.map (CommRingCat.ofHom (algebraMap (ArithmeticBase.CM.Generic.F q) L))) ≫
      ArithmeticBase.CM.Generic.fractionBase (q := q) ≫ l.map := by
  have hp : (z).left ≫ pullback.fst (M.integral a).toOver.hom M.arithmetic.generic =
      Spec.map (CommRingCat.ofHom (algebraMap (ArithmeticBase.CM.Generic.F q) L)) ≫ ArithmeticBase.CM.Generic.fractionBase (q := q) ≫ l.map :=
    FieldPoint.CM.fieldPoint_projection (L := L) (M.integral a).toOver sl
  exact (Category.assoc _ _ _).trans
    ((congrArg (Spec.map (CommRingCat.ofHom σ) ≫ ·) hp).trans (Category.assoc _ _ _).symm)

def sourceIso : AbelianScheme.TateComparison.PELModuli.PELFamilyIso
    ((Isogenies.NeighborCounting.Intrinsic.ReductionSpecification.genericSource (L := ArithmeticBase.CM.Generic.F q) l).pullback
      (Spec.map (CommRingCat.ofHom σ) ≫ Spec.map (CommRingCat.ofHom (algebraMap (ArithmeticBase.CM.Generic.F q) L))))
    ((PELSource.CM.heckeData M a C χ).fiberFamily
      (Spec.map (CommRingCat.ofHom σ) ≫ EvaluationGenericTest.CM.originalBase (L := L) j)
      (point M hM j hsplit R labels hlabels a hden p l C χ σ)) :=
  Source.PELFamily.CM.Family.sourceIso (M.integral a).universal.data l.map (ArithmeticBase.CM.Generic.fractionBase (q := q))
    (Spec.map (CommRingCat.ofHom σ) ≫ Spec.map (CommRingCat.ofHom (algebraMap (ArithmeticBase.CM.Generic.F q) L)))
    (pullback.fst (M.integral a).toOver.hom M.arithmetic.generic)
    (point M hM j hsplit R labels hlabels a hden p l C χ σ).left
    (point_projection M hM j hsplit R labels hlabels a hden p l C χ σ)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.SourceExtension.CM

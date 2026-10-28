import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.LiftRecovery
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.PELFamily
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Models
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ReductionSpecification
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IsogenyQuotientFibers

/-! # PEL Source -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.PELSource.CM

noncomputable section

/-! NeighborCounting and TateComparison use canonically isomorphic full PEL sources at the
actual generic point of the same Witt lift. The required projection
equality is proved by the original point construction. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ReductionSpecification
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.PointExt.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReductionPoints.CM
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
  (p : Geometric.PointExt.CM.pointBase (AlgebraicClosure (ZMod q)) ⟶ R.geometricFiber a)
  (l : Isogenies.NeighborCounting.Lifts.IntegralLift (FrobeniusKernelLifts.CM.reduction M hM j hsplit R labels hlabels a)
    (ArithmeticBase.CM.W (q := q)) (ArithmeticBase.CM.arithmeticMap (j := j) hden) (ArithmeticBase.CM.residueIso (q := q)) (ReductionPoints.CM.primeFieldPoint R a p))
  {L : Type} [Field L] [Algebra (ArithmeticBase.CM.Generic.F q) L]
  (C : AbelianScheme.TateComparison.Local.IntegralType M.s → AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence ((Over.pullback M.arithmetic.generic).obj (M.integral a).toOver))
  (χ : Fin M.s × Bool → NumberField.RingOfIntegers E →+* ℤ_[q])

abbrev heckeData : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E M.arithmetic.extension.carrier M.s q :=
  @Models.CM.Hecke.data E K _ _ _ _ _ M.s (M.level a) (M.datum a) M.iota M.complexEmbedding
    (M.moduli a).space (M.moduli a).universal M.arithmetic (M.integral a) (M.componentCount a)
    (M.components a) (M.decomposition a) q _ C χ
local notation "sl" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.LiftRecovery.CM.schemeLift M hM j hsplit R labels hlabels a hden p l

def sourceIso :
    AbelianScheme.TateComparison.PELModuli.PELFamilyIso ((Isogenies.NeighborCounting.Intrinsic.ReductionSpecification.genericSource (L := ArithmeticBase.CM.Generic.F q) l).pullback
      (Spec.map (CommRingCat.ofHom (algebraMap (ArithmeticBase.CM.Generic.F q) L))))
      ((heckeData M a C χ).fiberFamily (EvaluationGenericTest.CM.originalBase (L := L) j)
        (FieldPoint.CM.fieldPoint (M.integral a).toOver sl)) :=
  Source.PELFamily.CM.Family.sourceIso (M.integral a).universal.data l.map
    (ArithmeticBase.CM.Generic.fractionBase (q := q)) (Spec.map (CommRingCat.ofHom (algebraMap (ArithmeticBase.CM.Generic.F q) L)))
    (pullback.fst (M.integral a).toOver.hom M.arithmetic.generic)
    (FieldPoint.CM.fieldPoint (M.integral a).toOver sl).left
    (FieldPoint.CM.fieldPoint_projection (M.integral a).toOver sl)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.PELSource.CM

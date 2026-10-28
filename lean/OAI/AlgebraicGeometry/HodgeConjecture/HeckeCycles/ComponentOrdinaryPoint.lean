import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.OrdinaryEquiv
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.AlbaneseImage
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ComponentIntrinsicLift

/-! # Component Ordinary Point -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ComponentOrdinaryPoint.CM.Ordinary

noncomputable section

/-! Give an original ordinary component point the literal prime-field
source used by its native Witt lift. The ordinary-point equivalence is
proved to identify this point with the original component label. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.PointExt.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReductionPoints.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM.Generic
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.Locus.CM

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
  (c : Fin (M.componentCount a))
  (p : Geometric.PointExt.CM.pointBase (AlgebraicClosure (ZMod q)) ⟶ Ordinary.Locus.CM.componentFiber R a c)

  (hord : p.left (IsLocalRing.closedPoint (AlgebraicClosure (ZMod q))) ∈ Ordinary.Locus.CM.componentOrdinaryLocus R a c)

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.Detection.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SpecialOrdinaryFrobenius.CM.Ordinary

def original : Intrinsic.Detection.CM.ordinaryPoints R a := ⟨c, ⟨p, hord⟩⟩

local notation "e" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.OrdinaryEquiv.CM.IntrinsicOrdinary.pointEquiv M hM j hsplit R labels hlabels a

def native : (FrobeniusKernelLifts.CM.reduction M hM j hsplit R labels hlabels a).OrdinaryPoint := by
  let x := original M j R a c p hord
  have hv := Intrinsic.OrdinaryEquiv.CM.IntrinsicOrdinary.pointEquiv_val M hM j hsplit R labels hlabels a x
  exact ⟨ReductionPoints.CM.primeFieldPoint R a (p ≫ Ordinary.Locus.CM.componentFiberInclusion R a c), hv ▸ (e x).property⟩

theorem native_val : (native M hM j hsplit R labels hlabels a c p hord).val =
    ReductionPoints.CM.primeFieldPoint R a (p ≫ Ordinary.Locus.CM.componentFiberInclusion R a c) := rfl

theorem native_eq : native M hM j hsplit R labels hlabels a c p hord =
    e (original M j R a c p hord) := by
  apply Subtype.ext
  exact (native_val M hM j hsplit R labels hlabels a c p hord).trans
    (Intrinsic.OrdinaryEquiv.CM.IntrinsicOrdinary.pointEquiv_val M hM j hsplit R labels hlabels a
      (original M j R a c p hord)).symm

theorem image_eq :
    Additive.ofMul (ReductionPoints.CM.primeFieldPoint R a (p ≫ Ordinary.Locus.CM.componentFiberInclusion R a c) ≫
      (Over.pullback R.specialBase).map
        (TotalAlbaneseMap.CM.map (M.components a) (M.decomposition a))) =
      SpecialOrdinaryFrobenius.CM.Ordinary.ordinaryImage R a (original M j R a c p hord) :=
  Ordinary.AlbaneseImage.CM.image_eq R a (original M j R a c p hord)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ComponentOrdinaryPoint.CM.Ordinary

import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.OrdinaryImage
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.OperatorTransport

/-! # Ordinary Sums -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.OrdinarySums.CM.IntrinsicOrdinaryRaw

noncomputable section

/-! The native NeighborCounting ordinary neighbor sums become the exact sums used
for detection. The point equivalence, Frobenius compatibility and total
Albanese image comparison are all proved before this transport. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.Detection.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.Frobenius.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SpecialOrdinaryFrobenius.CM.Ordinary

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  (M : PELModuli.CMPoints.Models.RankThreePELModel E K) (hM : M.HasPrescribedBallPeriods)
  {q : ℕ} [Fact q.Prime] (j : M.QadicChoice q)
  (hsplit : j.HasSplitCoordinates M.extendedEmbedding)
  (R : M.GoodIntegralReduction q j)
  (labels : (Fin M.s × Bool) ≃ Gal(E/ℚ))
  (hlabels : ∀ (v : Fin M.s) (b : Bool),
    labels (v, !b) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels (v, b))
  (a : M.Family)

local notation "D" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FrobeniusKernelLifts.CM.reduction M hM j hsplit R labels hlabels a

local notation "e" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.OrdinaryEquiv.CM.IntrinsicOrdinary.pointEquiv M hM j hsplit R labels hlabels a

variable (hs : Smooth (M.integral a).toOver.hom)
  (Z : (FrobeniusKernelLifts.CM.reduction M hM j hsplit R labels hlabels a).OrdinaryPoint →
    (FrobeniusKernelLifts.CM.reduction M hM j hsplit R labels hlabels a).OrdinaryPoint)
  (Y : (FrobeniusKernelLifts.CM.reduction M hM j hsplit R labels hlabels a).OrdinaryPoint →
    Multiset (FrobeniusKernelLifts.CM.reduction M hM j hsplit R labels hlabels a).OrdinaryPoint)

local instance : GrpObj (Frobenius.CM.specialAlbanese R a).X := (Frobenius.CM.specialAlbanese R a).grp
local instance : IsCommMonObj (Frobenius.CM.specialAlbanese R a).X := (Frobenius.CM.specialAlbanese R a).comm

def image (x : (D).OrdinaryPoint) : Additive (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBase q ⟶ (Frobenius.CM.specialAlbanese R a).X) :=
  Additive.ofMul (x.val ≫ (Over.pullback R.specialBase).map
    (TotalAlbaneseMap.CM.map (M.components a) (M.decomposition a)))

theorem image_equiv (x : Detection.CM.ordinaryPoints R a) :
    image M hM j hsplit R labels hlabels a (e x) = SpecialOrdinaryFrobenius.CM.Ordinary.ordinaryImage R a x :=
  (OrdinaryImage.CM.IntrinsicOrdinary.image_eq M hM j hsplit R labels hlabels a (e x)).trans
    (congrArg (SpecialOrdinaryFrobenius.CM.Ordinary.ordinaryImage R a) ((e).symm_apply_apply x))

theorem rawSums (i : Fin 3) (x : Detection.CM.ordinaryPoints R a) :
    ((RepresentationTheory.Hecke.CubicRelation.ordinaryRawNeighbors (O := (D).OrdinaryPoint) q (D).ordinaryFrobenius Z Y i (e x)).map
      (image M hM j hsplit R labels hlabels a)).sum =
    ((RepresentationTheory.Hecke.CubicRelation.ordinaryRawNeighbors (O := Detection.CM.ordinaryPoints R a) q (Ordinary.PointFrobenius.CM.ordinaryFrobenius R a hs)
      (Ordinary.OperatorTransport.CM.pointOperator e Z) (Ordinary.OperatorTransport.CM.multisetOperator e Y)
      i x).map (SpecialOrdinaryFrobenius.CM.Ordinary.ordinaryImage R a)).sum := by
  have hn := Ordinary.OperatorTransport.CM.rawNeighbors e q
    (Ordinary.PointFrobenius.CM.ordinaryFrobenius R a hs) (D).ordinaryFrobenius Z Y
    (OrdinaryEquiv.CM.IntrinsicOrdinary.frobenius M hM j hsplit R labels hlabels a hs) i x
  have h := congrArg (fun m => (m.map (image M hM j hsplit R labels hlabels a)).sum) hn
  simpa only [Multiset.map_map, Function.comp_def, image_equiv] using h.symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.OrdinarySums.CM.IntrinsicOrdinaryRaw

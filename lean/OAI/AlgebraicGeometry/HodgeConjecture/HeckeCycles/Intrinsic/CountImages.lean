import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.OrdinarySums
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CommonPairImages

/-! # Count Images -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.CountImages.CM

noncomputable section

/-! Apply the actual total Albanese map to the native reduction counts
and obtain exactly the component-labelled sums used by detection. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.Detection.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.Frobenius.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SpecialOrdinaryFrobenius.CM.Ordinary

variable {E K : Type} [Field E] [NumberField E]
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

theorem map_factor {I S A : Type} (xs : Multiset I) (f : I → S) (a : S → A) (b : I → A)
    (h : ∀ i, a (f i) = b i) : (xs.map f).map a = xs.map b := by
  rw [Multiset.map_map]
  exact Multiset.map_congr rfl (fun i _ => h i)

def nativePointImage (x : (D).GeometricPoint) : Additive (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBase q ⟶ (Frobenius.CM.specialAlbanese R a).X) :=
  CommonPairImages.CM.pointImage R a x

def sumImages (m : Multiset (D).GeometricPoint) : Additive (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBase q ⟶ (Frobenius.CM.specialAlbanese R a).X) :=
  (m.map (nativePointImage M hM j hsplit R labels hlabels a)).sum

theorem from_native_counts (i : Fin 3) (x : Detection.CM.ordinaryPoints R a) (m : Multiset (D).GeometricPoint)
    (h : m = (RepresentationTheory.Hecke.CubicRelation.ordinaryRawNeighbors (O := (D).OrdinaryPoint) q (D).ordinaryFrobenius Z Y i (e x)).map Subtype.val) :
    sumImages M hM j hsplit R labels hlabels a m =
      ((RepresentationTheory.Hecke.CubicRelation.ordinaryRawNeighbors (O := Detection.CM.ordinaryPoints R a) q (Ordinary.PointFrobenius.CM.ordinaryFrobenius R a hs)
        (Ordinary.OperatorTransport.CM.pointOperator e Z) (Ordinary.OperatorTransport.CM.multisetOperator e Y)
        i x).map (SpecialOrdinaryFrobenius.CM.Ordinary.ordinaryImage R a)).sum := by
  have hm := congrArg (sumImages M hM j hsplit R labels hlabels a) h
  have hf := map_factor
    (RepresentationTheory.Hecke.CubicRelation.ordinaryRawNeighbors (O := (D).OrdinaryPoint) q (D).ordinaryFrobenius Z Y i (e x))
    Subtype.val (nativePointImage M hM j hsplit R labels hlabels a)
    (OrdinarySums.CM.IntrinsicOrdinaryRaw.image M hM j hsplit R labels hlabels a) (fun _ => rfl)
  exact hm.trans ((congrArg Multiset.sum hf).trans
    (OrdinarySums.CM.IntrinsicOrdinaryRaw.rawSums M hM j hsplit R labels hlabels a hs Z Y i x))

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.CountImages.CM

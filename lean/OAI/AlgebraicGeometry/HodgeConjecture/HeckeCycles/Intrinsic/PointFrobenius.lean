import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PrimeFieldPoints
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReductionPoints
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.Frobenius

/-! # Point Frobenius -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.PointFrobenius.CM

noncomputable section

/-! Frobenius on the actual geometric source fibers is transported from
the prime-field geometric-point functor. Naturality preserves every
component inclusion, and the full torsion-group isomorphism preserves
the actual CMPoints ordinary locus. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.PointExt.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReductionPoints.CM

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {M : PELModuli.CMPoints.Models.RankThreePELModel E K} {q : ℕ} [Fact q.Prime]
  {j : M.QadicChoice q} (R : M.GoodIntegralReduction q j)

def pointsEquiv (X : Over M.arithmetic.base) :
    (Geometric.PointExt.CM.pointBase (AlgebraicClosure (ZMod q)) ⟶ (Over.pullback R.geometricBase).obj X) ≃
      (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBase q ⟶ (Over.pullback R.specialBase).obj X) :=
  PrimeFieldPoints.CM.pointEquiv R.specialBase (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBase q).hom R.geometricBase
    (Frobenius.CM.geometricBase_factor R) X

theorem pointsEquiv_map {X Y : Over M.arithmetic.base} (a : X ⟶ Y)
    (p : Geometric.PointExt.CM.pointBase (AlgebraicClosure (ZMod q)) ⟶ (Over.pullback R.geometricBase).obj X) :
    pointsEquiv R Y (p ≫ (Over.pullback R.geometricBase).map a) =
      pointsEquiv R X p ≫ (Over.pullback R.specialBase).map a :=
  PrimeFieldPoints.CM.pointEquiv_map R.specialBase (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBase q).hom R.geometricBase
    (Frobenius.CM.geometricBase_factor R) a p

theorem pointsEquiv_eq_primeFieldPoint (a : M.Family)
    (p : Geometric.PointExt.CM.pointBase (AlgebraicClosure (ZMod q)) ⟶ R.geometricFiber a) :
    pointsEquiv R (M.integral a).toOver p = ReductionPoints.CM.primeFieldPoint R a p := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact (PrimeFieldPoints.CM.pointEquiv_projection R.specialBase (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBase q).hom
      R.geometricBase (Frobenius.CM.geometricBase_factor R) (M.integral a).toOver p).trans
        (ReductionPoints.CM.primeFieldPoint_projection R a p).symm
  · exact (pointsEquiv R (M.integral a).toOver p).w.trans (ReductionPoints.CM.primeFieldPoint R a p).w.symm

def pointFrobenius (X : Over M.arithmetic.base)
    (p : Geometric.PointExt.CM.pointBase (AlgebraicClosure (ZMod q)) ⟶ (Over.pullback R.geometricBase).obj X) :
    Geometric.PointExt.CM.pointBase (AlgebraicClosure (ZMod q)) ⟶ (Over.pullback R.geometricBase).obj X :=
  (pointsEquiv R X).symm ((AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBaseFrobenius q).hom ≫ pointsEquiv R X p)

theorem pointsEquiv_frobenius (X : Over M.arithmetic.base)
    (p : Geometric.PointExt.CM.pointBase (AlgebraicClosure (ZMod q)) ⟶ (Over.pullback R.geometricBase).obj X) :
    pointsEquiv R X (pointFrobenius R X p) =
      (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBaseFrobenius q).hom ≫ pointsEquiv R X p :=
  (pointsEquiv R X).apply_symm_apply _

theorem pointFrobenius_map {X Y : Over M.arithmetic.base} (a : X ⟶ Y)
    (p : Geometric.PointExt.CM.pointBase (AlgebraicClosure (ZMod q)) ⟶ (Over.pullback R.geometricBase).obj X) :
    pointFrobenius R Y (p ≫ (Over.pullback R.geometricBase).map a) =
      pointFrobenius R X p ≫ (Over.pullback R.geometricBase).map a := by
  apply (pointsEquiv R Y).injective
  rw [pointsEquiv_frobenius, pointsEquiv_map, pointsEquiv_map,
    pointsEquiv_frobenius, Category.assoc]

theorem primeFieldPoint_frobenius (a : M.Family)
    (p : Geometric.PointExt.CM.pointBase (AlgebraicClosure (ZMod q)) ⟶ R.geometricFiber a) :
    ReductionPoints.CM.primeFieldPoint R a (pointFrobenius R (M.integral a).toOver p) =
      (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBaseFrobenius q).hom ≫ ReductionPoints.CM.primeFieldPoint R a p :=
  (pointsEquiv_eq_primeFieldPoint R a (pointFrobenius R (M.integral a).toOver p)).symm.trans
    ((pointsEquiv_frobenius R (M.integral a).toOver p).trans
      (congrArg ((AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBaseFrobenius q).hom ≫ ·) (pointsEquiv_eq_primeFieldPoint R a p)))

theorem pointFrobenius_preserves_ordinarity (a : M.Family)
    (hs : Smooth (M.integral a).toOver.hom)
    (p : Geometric.PointExt.CM.pointBase (AlgebraicClosure (ZMod q)) ⟶ R.geometricFiber a) :
    R.IsOrdinary a ((pointFrobenius R (M.integral a).toOver p).left
      (IsLocalRing.closedPoint (AlgebraicClosure (ZMod q)))) ↔
        R.IsOrdinary a (p.left (IsLocalRing.closedPoint (AlgebraicClosure (ZMod q)))) := by
  let fp : Geometric.PointExt.CM.pointBase (AlgebraicClosure (ZMod q)) ⟶ R.geometricFiber a :=
    pointFrobenius R (M.integral a).toOver p
  let z := ReductionPoints.CM.primeFieldPoint R a p
  let e : Over.mk ((AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBaseFrobenius q).hom ≫ z).left ≅ Over.mk z.left :=
    Over.isoMk ((Over.forget _).mapIso (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBaseFrobenius q)) rfl
  have hc := Nat.card_congr
    (((ReductionPoints.CM.primeFieldAbelian R a).torsionFunctor q).mapIso e.op).groupIsoToMulEquiv.toEquiv
  have hcard : Nat.card ((ReductionPoints.CM.primeFieldAbelian R a).torsionPoints q (Over.mk (ReductionPoints.CM.primeFieldPoint R a fp).left)) =
      Nat.card ((ReductionPoints.CM.primeFieldAbelian R a).torsionPoints q (Over.mk (ReductionPoints.CM.primeFieldPoint R a p).left)) :=
    (congrArg (fun w : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBase q ⟶ R.specialFiber a =>
      Nat.card ((ReductionPoints.CM.primeFieldAbelian R a).torsionPoints q (Over.mk w.left)))
      (primeFieldPoint_frobenius R a p)).trans hc.symm
  exact (ReductionPoints.CM.isOrdinary_iff_primeFieldPoint_count R a hs fp).trans
    ((iff_of_eq (congrArg (fun n : ℕ => n = q ^ (3 * M.s)) hcard)).trans
      (ReductionPoints.CM.isOrdinary_iff_primeFieldPoint_count R a hs p).symm)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.PointFrobenius.CM

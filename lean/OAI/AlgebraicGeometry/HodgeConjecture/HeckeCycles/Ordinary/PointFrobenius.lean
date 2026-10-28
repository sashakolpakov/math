import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.PointFrobenius

/-! # Point Frobenius -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.PointFrobenius.CM

noncomputable section

/-! Frobenius is an actual operator on the dense ordinary points used
for Albanese detection. Its component-preservation property is proved
from the native component maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.PointExt.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.Locus.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.Detection.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.PointFrobenius.CM

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {M : PELModuli.CMPoints.Models.RankThreePELModel E K} {q : ℕ} [Fact q.Prime]
  {j : M.QadicChoice q} (R : M.GoodIntegralReduction q j) (a : M.Family)
  (hs : Smooth (M.integral a).toOver.hom)

def ordinaryFrobenius (x : Intrinsic.Detection.CM.ordinaryPoints R a) : Intrinsic.Detection.CM.ordinaryPoints R a := by
  let p : Geometric.PointExt.CM.pointBase (AlgebraicClosure (ZMod q)) ⟶ Locus.CM.componentFiber R a x.1 := x.2.val
  let fp : Geometric.PointExt.CM.pointBase (AlgebraicClosure (ZMod q)) ⟶ Locus.CM.componentFiber R a x.1 :=
    Intrinsic.PointFrobenius.CM.pointFrobenius R ((M.components a).S x.1) p
  let t : Geometric.PointExt.CM.pointBase (AlgebraicClosure (ZMod q)) ⟶ R.geometricFiber a :=
    p ≫ Locus.CM.componentFiberInclusion R a x.1
  have ht : R.IsOrdinary a (t.left (IsLocalRing.closedPoint (AlgebraicClosure (ZMod q)))) :=
    x.2.property
  have hf := (Intrinsic.PointFrobenius.CM.pointFrobenius_preserves_ordinarity R a hs t).mpr ht
  have hn : Intrinsic.PointFrobenius.CM.pointFrobenius R (M.integral a).toOver t =
      fp ≫ Locus.CM.componentFiberInclusion R a x.1 :=
    Intrinsic.PointFrobenius.CM.pointFrobenius_map R (Locus.CM.componentInclusion (M.components a) (M.decomposition a) x.1) p
  refine ⟨x.1, fp, ?_⟩
  exact (congrArg (fun z : Geometric.PointExt.CM.pointBase (AlgebraicClosure (ZMod q)) ⟶ R.geometricFiber a =>
    R.IsOrdinary a (z.left (IsLocalRing.closedPoint (AlgebraicClosure (ZMod q))))) hn).mp hf

theorem ordinaryFrobenius_component (x : Intrinsic.Detection.CM.ordinaryPoints R a) :
    (ordinaryFrobenius R a hs x).1 = x.1 := rfl

theorem ordinaryFrobenius_point (x : Intrinsic.Detection.CM.ordinaryPoints R a) :
    (ordinaryFrobenius R a hs x).2.val =
      Intrinsic.PointFrobenius.CM.pointFrobenius R ((M.components a).S x.1) x.2.val := rfl

theorem ordinaryFrobenius_total (x : Intrinsic.Detection.CM.ordinaryPoints R a) :
    ReductionPoints.CM.primeFieldPoint R a
      ((ordinaryFrobenius R a hs x).2.val ≫ Locus.CM.componentFiberInclusion R a x.1) =
      (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBaseFrobenius q).hom ≫ ReductionPoints.CM.primeFieldPoint R a
        (x.2.val ≫ Locus.CM.componentFiberInclusion R a x.1) := by
  have hn := Intrinsic.PointFrobenius.CM.pointFrobenius_map R
    (Locus.CM.componentInclusion (M.components a) (M.decomposition a) x.1) x.2.val
  exact (congrArg (ReductionPoints.CM.primeFieldPoint R a) hn.symm).trans
    (Intrinsic.PointFrobenius.CM.primeFieldPoint_frobenius R a (x.2.val ≫ Locus.CM.componentFiberInclusion R a x.1))

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.PointFrobenius.CM

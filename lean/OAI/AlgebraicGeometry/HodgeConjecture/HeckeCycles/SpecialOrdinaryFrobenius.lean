import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.PointFrobenius
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FrobeniusPointAction
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointEvaluation

/-! # Special Ordinary Frobenius -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SpecialOrdinaryFrobenius.CM.Ordinary

noncomputable section

/-! Frobenius on ordinary Albanese points, evaluated directly in the
geometric point functor of the actual prime-field Albanese product. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.Detection.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.Frobenius.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.PointFrobenius.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.PointFrobenius.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProductPoints.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointSpecializationFormula.CM.Points
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FieldFrobenius.CM

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {M : PELModuli.CMPoints.Models.RankThreePELModel E K} {q : ℕ} [Fact q.Prime]
  {j : M.QadicChoice q} (R : M.GoodIntegralReduction q j) (a : M.Family)

def componentAlbaneseMap (i : Fin (M.componentCount a)) :
    (Over.pullback R.specialBase).obj ((M.components a).S i) ⟶ (Intrinsic.Frobenius.CM.specialAlbanese R a).X :=
  (Over.pullback R.specialBase).map ((M.components a).a i ≫ ProductPoints.CM.factorMap (M.components a).A i)

def ordinaryImage (x : Intrinsic.Detection.CM.ordinaryPoints R a) :
    Additive (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBase q ⟶ (Intrinsic.Frobenius.CM.specialAlbanese R a).X) :=
  Additive.ofMul (Intrinsic.PointFrobenius.CM.pointsEquiv R ((M.components a).S x.1) x.2.val ≫ componentAlbaneseMap R a x.1)

theorem ordinaryImage_frobenius (hs : Smooth (M.integral a).toOver.hom)
    (x : Intrinsic.Detection.CM.ordinaryPoints R a) :
    (ordinaryImage R a (Ordinary.PointFrobenius.CM.ordinaryFrobenius R a hs x)).toMul =
      (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBaseFrobenius q).hom ≫ (ordinaryImage R a x).toMul := by
  have h := congrArg (· ≫ componentAlbaneseMap R a x.1)
    (Intrinsic.PointFrobenius.CM.pointsEquiv_frobenius R ((M.components a).S x.1) x.2.val)
  exact h.trans (Category.assoc _ _ _)

theorem integralFrobenius_on_ordinaryImage (hs : Smooth (M.integral a).toOver.hom)
    (x : Intrinsic.Detection.CM.ordinaryPoints R a) :
    PointSpecializationFormula.CM.Points.evaluateAt (Intrinsic.Frobenius.CM.specialAlbanese R a) (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBase q) (Finite.FieldFrobenius.CM.integralFrobenius (Intrinsic.Frobenius.CM.specialAlbanese R a))
      (ordinaryImage R a x) = ordinaryImage R a (Ordinary.PointFrobenius.CM.ordinaryFrobenius R a hs x) := by
  have h := FrobeniusPointAction.CM.frobenius_albanese_point q (Intrinsic.Frobenius.CM.specialAlbanese R a)
    (componentAlbaneseMap R a x.1) (Intrinsic.PointFrobenius.CM.pointsEquiv R ((M.components a).S x.1) x.2.val)
  apply Additive.toMul.injective
  exact (congrArg Additive.toMul h).trans
    ((Category.assoc _ _ _).trans (ordinaryImage_frobenius R a hs x).symm)

theorem algebraicFrobenius_on_ordinaryImage (hs : Smooth (M.integral a).toOver.hom)
    (x : Intrinsic.Detection.CM.ordinaryPoints R a) :
    PointEvaluation.CM.action (Intrinsic.Frobenius.CM.specialAlbanese R a) (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBase q)
      (FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius (ZMod q) (Intrinsic.Frobenius.CM.specialAlbanese R a).X)
      (ordinaryImage R a x) = ordinaryImage R a (Ordinary.PointFrobenius.CM.ordinaryFrobenius R a hs x) :=
  (congrArg (fun f : AddMonoid.End (Additive (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBase q ⟶ (Intrinsic.Frobenius.CM.specialAlbanese R a).X)) =>
    f (ordinaryImage R a x))
      (PointEvaluation.CM.action_frobenius (Intrinsic.Frobenius.CM.specialAlbanese R a) (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBase q))).trans
    (integralFrobenius_on_ordinaryImage R a hs x)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SpecialOrdinaryFrobenius.CM.Ordinary

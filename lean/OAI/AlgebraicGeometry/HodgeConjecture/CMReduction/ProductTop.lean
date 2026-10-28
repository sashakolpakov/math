import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.PackedRegroup
import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.MiddleTop
import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.Projection

/-! # Product Top -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMReduction

noncomputable section

/-! The exterior product of two nonzero top classes is a nonzero top
class on the actual product, by canonical Kunneth and the product dimension. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits CartesianMonoidalCategory

theorem EvenAlgebra.CM.Construction.EvenClass.inDegree_ne_zero {X : TopCat.{0}} (a : EvenAlgebra.CM.Construction.EvenClass (R := ℂ) X)
    (p : ℕ) (hp : a.1 = p) (ha : a.2 ≠ 0) : a.inDegree p hp ≠ 0 := by
  intro hz
  apply ha
  exact MiddleTop.CM.Construction.cohomologyCast_injective (K := ℂ) X (congrArg (fun n => n + n) hp)
    (hz.trans (map_zero _).symm)

def ProductTop.CM.Construction.productTopClass (S T : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (a : S.complexCohomology (S.complexDimension + S.complexDimension))
    (b : T.complexCohomology (T.complexDimension + T.complexDimension)) :
    (Albanese.Construction.SegreClosed.tensorIntegralProjectiveVariety S T).complexCohomology
      ((Albanese.Construction.SegreClosed.tensorIntegralProjectiveVariety S T).complexDimension +
        (Albanese.Construction.SegreClosed.tensorIntegralProjectiveVariety S T).complexDimension) :=
  (PackedRegroup.CM.Construction.evenPullback (fst S.toOver T.toOver) (PackedRegroup.CM.Construction.packEven (Betti.Scheme.schemePointSpace S.toOver) S.complexDimension a) *
    PackedRegroup.CM.Construction.evenPullback (snd S.toOver T.toOver) (PackedRegroup.CM.Construction.packEven (Betti.Scheme.schemePointSpace T.toOver) T.complexDimension b)).inDegree
      (Albanese.Construction.SegreClosed.tensorIntegralProjectiveVariety S T).complexDimension
      (by exact (Products.CM.SurfaceConstruction.product_complexDimension S T).symm)

theorem ProductTop.CM.Construction.pack_productTopClass (S T : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (a : S.complexCohomology (S.complexDimension + S.complexDimension))
    (b : T.complexCohomology (T.complexDimension + T.complexDimension)) :
    PackedRegroup.CM.Construction.packEven (Betti.Scheme.schemePointSpace (Albanese.Construction.SegreClosed.tensorIntegralProjectiveVariety S T).toOver)
      (Albanese.Construction.SegreClosed.tensorIntegralProjectiveVariety S T).complexDimension (ProductTop.CM.Construction.productTopClass S T a b) =
    PackedRegroup.CM.Construction.evenPullback (fst S.toOver T.toOver) (PackedRegroup.CM.Construction.packEven (Betti.Scheme.schemePointSpace S.toOver) S.complexDimension a) *
      PackedRegroup.CM.Construction.evenPullback (snd S.toOver T.toOver) (PackedRegroup.CM.Construction.packEven (Betti.Scheme.schemePointSpace T.toOver) T.complexDimension b) :=
  PackedRegroup.CM.Construction.packEven_inDegree _ _ _

theorem ProductTop.CM.Construction.productTopClass_ne_zero (S T : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (a : S.complexCohomology (S.complexDimension + S.complexDimension))
    (b : T.complexCohomology (T.complexDimension + T.complexDimension))
    (ha : a ≠ 0) (hb : b ≠ 0) : ProductTop.CM.Construction.productTopClass S T a b ≠ 0 := by
  let W := Albanese.Construction.SegreClosed.tensorIntegralProjectiveVariety S T
  have hraw := Kunneth.CM.SurfaceConstruction.complex_exteriorCup_ne_zero
    (X := S.presentation) (Y := T.presentation) (Z := W.presentation)
    (fst S.toOver T.toOver) (snd S.toOver T.toOver) (tensorProductIsBinaryProduct _ _)
    (S.complexDimension + S.complexDimension) (T.complexDimension + T.complexDimension) a b ha hb
  apply EvenAlgebra.CM.Construction.EvenClass.inDegree_ne_zero
  intro hz
  change ComplexOperations.CM.Construction.evenCup ℂ (Betti.Scheme.schemePointSpace W.toOver) S.complexDimension T.complexDimension
    (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) _ (fst S.toOver T.toOver) a)
    (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) _ (snd S.toOver T.toOver) b) = 0 at hz
  apply hraw
  exact MiddleTop.CM.Construction.cohomologyCast_injective (K := ℂ) (Betti.Scheme.schemePointSpace W.toOver)
    (add_add_add_comm S.complexDimension S.complexDimension T.complexDimension T.complexDimension)
    (hz.trans (map_zero _).symm)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMReduction

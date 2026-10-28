import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.OrdinaryEquiv
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.AlbaneseImage

/-! # Ordinary Image -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.OrdinaryImage.CM.IntrinsicOrdinary

noncomputable section

/-! Evaluate a native ordinary target in the actual total Albanese.
Its image is the original component-labelled image under the constructed
ordinary-point equivalence, so native neighbor counts can be used by the
detection theorem without a new Albanese-matching assumption. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.Detection.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SpecialOrdinaryFrobenius.CM.Ordinary

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

theorem image_eq (x : (D).OrdinaryPoint) :
    Additive.ofMul (x.val ≫ (Over.pullback R.specialBase).map
      (TotalAlbaneseMap.CM.map (M.components a) (M.decomposition a))) =
        SpecialOrdinaryFrobenius.CM.Ordinary.ordinaryImage R a ((e).symm x) := by
  let y := (e).symm x
  have hy : e y = x := (e).apply_symm_apply x
  have hs : x.val = Ordinary.AlbaneseImage.CM.sourcePoint R a y :=
    (congrArg Subtype.val hy).symm.trans
      (OrdinaryEquiv.CM.IntrinsicOrdinary.pointEquiv_val M hM j hsplit R labels hlabels a y)
  exact (congrArg (fun p : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBase q ⟶ R.specialFiber a => Additive.ofMul
    (p ≫ (Over.pullback R.specialBase).map
      (TotalAlbaneseMap.CM.map (M.components a) (M.decomposition a)))) hs).trans
        (Ordinary.AlbaneseImage.CM.image_eq R a y)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.OrdinaryImage.CM.IntrinsicOrdinary

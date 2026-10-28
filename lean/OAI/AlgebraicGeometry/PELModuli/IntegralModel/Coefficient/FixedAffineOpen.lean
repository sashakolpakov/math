import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.FixedOpenModels
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.EventualAffine
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.CompactOpenFinitePresentation
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Open.AffineBaseChange

/-! # Fixed Affine Open -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.FixedAffineOpen

noncomputable section

/-! An affine open of the generic fiber spreads as an actual affine
open inside a coefficient enlargement of the fixed ambient model. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

namespace Coefficients
variable {R K : Type} [CommRing R] [Field K] [Algebra R K]

theorem affine_open_in_fixed_model {X : Over (Spec (.of K))}
    (hX : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism X.hom) (M : Models.Coefficients.CoefficientModel R K X)
    (U : X.left.Opens) (hU : IsAffineOpen U) :
    ∃ (t : Finset K) (h : M.coefficients ⊆ t)
      (V : ((Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K h)).obj M.model).left.Opens),
      IsAffineOpen V ∧ Morphisms.Coefficients.genericModelLift M.model M.specialization M.cartesian.w h ⁻¹ᵁ V = U := by
  obtain ⟨t, hMt, V, hV, hpre⟩ := FixedOpenModels.Coefficients.compact_open_in_fixed_model M U hU.isCompact
  let Y := (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K hMt)).obj M.model
  let p := Morphisms.Coefficients.genericModelLift M.model M.specialization M.cartesian.w hMt
  have hp := Morphisms.Coefficients.genericModelLift_cartesian M.model M.specialization M.cartesian hMt
  let W : Over (Spec (.of K)) := Over.mk (U.ι ≫ X.hom)
  let W₀ : Over (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R K t) := Over.mk (V.ι ≫ Y.hom)
  let a := p.resLE V U hpre.ge
  have ha : IsPullback a U.ι V.ι p := IsOpenImmersion.isPullback _ _ _ _
    (Scheme.Hom.resLE_comp_ι p hpre.ge).symm (by simpa using hpre)
  have hW₀ : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism W₀.hom := CompactOpenFinitePresentation.compact_open_finitePresentation Y
    (Finiteness.Coefficients.baseChange_finitePresentation _ _ M.finitePresentation) V hV
  let A := Models.Coefficients.CoefficientModel.ofCartesian (X := W) t W₀ hW₀ a (ha.paste_vert hp)
  have : IsAffine W.left := hU
  obtain ⟨z, htz, hz⟩ := EventualAffine.Coefficients.coefficient_model_eventually_affine
    (CompactOpenFinitePresentation.compact_open_finitePresentation X hX U hU.isCompact) A
  change t ⊆ z at htz
  change IsAffine (pullback W₀.hom (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K htz)) at hz
  let b := ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K htz
  let π := pullback.fst Y.hom b
  have hW : IsAffineOpen (π ⁻¹ᵁ V) := Open.AffineBaseChange.baseChange_open_affine b Y V hz
  let e := BaseChange.Coefficients.coefficientBaseChangeTrans hMt htz M.model
  have : IsIso e.inv.left := ((Over.forget (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R K z)).mapIso e).isIso_inv
  refine ⟨z, hMt.trans htz, e.inv.left ⁻¹ᵁ (π ⁻¹ᵁ V), hW.preimage_of_isIso e.inv.left, ?_⟩
  have he : (Morphisms.Coefficients.genericModelLift M.model M.specialization M.cartesian.w (hMt.trans htz) ≫
      e.inv.left) ≫ π = p := by
    dsimp only [e, π, p, Y, b]
    rw [CommonStage.Coefficients.genericModelLift_trans_inv, Morphisms.Coefficients.genericModelLift_fst]
  rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, he]
  exact hpre

end Coefficients

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.FixedAffineOpen

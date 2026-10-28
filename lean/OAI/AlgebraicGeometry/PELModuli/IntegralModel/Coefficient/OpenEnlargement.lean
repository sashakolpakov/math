import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.CommonStage
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Open Enlargement -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.OpenEnlargement

noncomputable section

/-! Affine opens in a fixed coefficient model retain their generic
inverse images after any further coefficient enlargement. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

namespace Coefficients
variable {R K : Type} [CommRing R] [Field K] [Algebra R K]
    {X : Over (Spec (.of K))} (M : Models.Coefficients.CoefficientModel R K X)
    {t z : Finset K} (hMt : M.coefficients ⊆ t) (htz : t ⊆ z)
    (U : ((Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K hMt)).obj M.model).left.Opens)

def enlargedModelOpen :
    ((Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K (hMt.trans htz))).obj M.model).left.Opens :=
  (BaseChange.Coefficients.coefficientBaseChangeTrans hMt htz M.model).inv.left ⁻¹ᵁ
    (pullback.fst ((Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K hMt)).obj M.model).hom
      (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K htz) ⁻¹ᵁ U)

theorem enlargedModelOpen_affine (hU : IsAffineOpen U) :
    IsAffineOpen (enlargedModelOpen M hMt htz U) := by
  let Y := (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K hMt)).obj M.model
  let π := pullback.fst Y.hom (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K htz)
  let e := BaseChange.Coefficients.coefficientBaseChangeTrans hMt htz M.model
  have : IsAffineHom (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K htz) := inferInstance
  have : IsAffineHom π := MorphismProperty.pullback_fst Y.hom
    (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K htz) (inferInstanceAs (IsAffineHom (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K htz)))
  have : IsIso e.inv.left := ((Over.forget (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R K z)).mapIso e).isIso_inv
  exact (hU.preimage π).preimage_of_isIso e.inv.left

theorem enlargedModelOpen_generic :
    Coefficient.Morphisms.Coefficients.genericModelLift M.model M.specialization M.cartesian.w (hMt.trans htz) ⁻¹ᵁ
      enlargedModelOpen M hMt htz U =
    Coefficient.Morphisms.Coefficients.genericModelLift M.model M.specialization M.cartesian.w hMt ⁻¹ᵁ U := by
  unfold enlargedModelOpen
  rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage,
    CommonStage.Coefficients.genericModelLift_trans_inv, Coefficient.Morphisms.Coefficients.genericModelLift_fst]

end Coefficients

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.OpenEnlargement

import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.OpenModels
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.Morphisms

/-! # Fixed Open Models -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.FixedOpenModels

noncomputable section

/-! A compact generic open descends inside the actual base change
of a fixed coefficient model, preserving its generic inverse image. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

namespace Coefficients
variable {R K : Type} [CommRing R] [Field K] [Algebra R K]

theorem compact_open_in_fixed_model {X : Over (Spec (.of K))}
    (M : Models.Coefficients.CoefficientModel R K X) (U : X.left.Opens) (hU : IsCompact (U : Set X.left)) :
    ∃ (t : Finset K) (h : M.coefficients ⊆ t)
      (V : ((Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K h)).obj M.model).left.Opens),
      IsCompact (V : Set ((Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K h)).obj M.model).left) ∧
      Morphisms.Coefficients.genericModelLift M.model M.specialization M.cartesian.w h ⁻¹ᵁ V = U := by
  let e := M.expansionGenericIso
  have hU' : IsCompact (e.inv ⁻¹ᵁ U : Set (ArithmeticGeometry.Models.Descent.Constructions.Foundations.expansionCone R K M.coefficients M.model).pt) :=
    e.inv.isCompact_preimage hU
  obtain ⟨i, V, hV, hi⟩ := ArithmeticGeometry.Models.Descent.Constructions.Foundations.compact_open_descends R K M.coefficients M.model (e.inv ⁻¹ᵁ U) hU'
  let h : M.coefficients ⊆ i.left.unop := leOfHom i.hom.unop
  let σ := pullbackSymmetry M.model.hom (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K h)
  refine ⟨i.left.unop, h, σ.hom ⁻¹ᵁ V, σ.hom.isCompact_preimage hV, ?_⟩
  rw [← Scheme.Hom.comp_preimage, Morphisms.Coefficients.genericModelLift_to_expansion M.model M.specialization M.cartesian i]
  change (e.hom ≫ (ArithmeticGeometry.Models.Descent.Constructions.Foundations.expansionCone R K M.coefficients M.model).π.app i) ⁻¹ᵁ V = U
  rw [Scheme.Hom.comp_preimage, hi, ← Scheme.Hom.comp_preimage, e.hom_inv_id]
  rfl

end Coefficients

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.FixedOpenModels

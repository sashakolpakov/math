import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.SingleCoefficientCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.TopClassCoefficients

/-! # Top Coefficient Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.TopCoefficientIso

noncomputable section

/-! The coefficient iso in original single-total coordinates is the
same exact homology comparison that carries the full-intersection class. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u uA vA uB vB
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  {ι : Type u} [LinearOrder ι] (U : ι → C)
  {A : Type uA} [Category.{vA} A] [Abelian A] [HasProducts.{u} A] [HasCoproducts.{0} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasProducts.{u} B] [HasCoproducts.{0} B]
  (G : A ⥤ B) [G.Additive] [G.PreservesHomology] [PreservesLimitsOfSize.{u,u} G]
  (P : Cᵒᵖ ⥤ A) (m : ℕ)

omit [HasCoproducts A] [HasCoproducts B] in
theorem eq :
    SingleCoefficientCoordinates.coefficientIso U (𝟭 (Cᵒᵖ ⥤ A)) G P m =
      TopClassCoefficients.homologyIso U G P m := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.TopCoefficientIso

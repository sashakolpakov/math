import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicOrdered.EdgeCoordinates

/-! # Edge Additive -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicOrdered.EdgeAdditive.IntrinsicCoordinates

noncomputable section

/-! Additive coordinate normalization of the native Čech edge. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
private theorem join {D : Type*} [Category D] {A B C E : D}
    {a : A ⟶ B} {b : B ⟶ C} {c : A ⟶ A} {d : A ⟶ C} {e : C ⟶ E} {f : A ⟶ E}
    (h : a ≫ b = c ≫ d) (hc : c = 𝟙 A) (he : d ≫ e = f) : a ≫ b ≫ e = f := by
  rw [← Category.assoc, h, hc, Category.id_comp, he]
universe u
variable {X S : Scheme.{u}} (π : X ⟶ S) [X.IsSeparated]
  {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : iSup U = ⊤)
  (K : CochainComplex X.Modules ℕ)
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicOrdered.CechAdditiveCoordinates.Intrinsic.forgetScalars (S := S)
attribute [local instance] EdgeCoordinates.Intrinsic.finiteBiproducts

abbrev additive := join (EdgeCoordinates.Intrinsic.mapped_linear π U hU K) (EdgeCoordinates.Intrinsic.forget_sectionsMap π K)
  (Ordered.EdgeCoefficient.edge U G (RelativeCech.CoefficientQuasiIso.coefficients π K))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicOrdered.EdgeAdditive.IntrinsicCoordinates

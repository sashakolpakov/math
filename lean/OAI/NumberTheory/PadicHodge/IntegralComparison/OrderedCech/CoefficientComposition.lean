import OAI.NumberTheory.PadicHodge.IntegralComparison.Ordered.SingleGlobalSourceCoefficients
import OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.HomologyComposition
import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.CoefficientComposition

/-! # Coefficient Composition -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.CoefficientComposition

noncomputable section

/-! The actual ordered Cech coefficient coordinates commute with
successive exact changes of the coefficient category. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Functor.HomologyComposition.composite_preservesHomology
universe u uA vA uB vB uD vD
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  {ι : Type u} [LinearOrder ι] (U : ι → C)
  {A : Type uA} [Category.{vA} A] [Abelian A] [HasProducts.{u} A] [HasCoproducts.{0} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasProducts.{u} B] [HasCoproducts.{0} B]
  {D : Type uD} [Category.{vD} D] [Abelian D] [HasProducts.{u} D] [HasCoproducts.{0} D]
  (F : A ⥤ B) (G : B ⥤ D) [F.Additive] [G.Additive]
  [F.PreservesHomology] [G.PreservesHomology]
  [PreservesLimitsOfSize.{u,u} F] [PreservesLimitsOfSize.{u,u} G]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (P : Cᵒᵖ ⥤ A)

omit [HasCoproducts A] [HasCoproducts B] [HasCoproducts D] [F.PreservesHomology] [G.PreservesHomology] [PreservesFiniteLimits G] [PreservesFiniteColimits G] in
theorem cochain :
    (G.mapHomologicalComplex (.up ℕ)).map (CoefficientChange.complexIso U F P).hom ≫
      (CoefficientChange.complexIso U G (P ⋙ F)).hom =
    (CoefficientChange.complexIso U (F ⋙ G) P).hom := by
  apply HomologicalComplex.Hom.ext
  funext q
  change G.map (piComparison F _) ≫ piComparison G _ = piComparison (F ⋙ G) _
  exact GeometricComparison.Cech.CoefficientComposition.CechCoefficientComposition.piComparison F G _

omit [HasCoproducts A] [HasCoproducts B] [HasCoproducts D] in
theorem homology (q : ℕ) :
    G.map (Ordered.SingleGlobalSourceCoefficients.coefficientIso F P U q).hom ≫
      (Ordered.SingleGlobalSourceCoefficients.coefficientIso G (P ⋙ F) U q).hom =
    (Ordered.SingleGlobalSourceCoefficients.coefficientIso (F ⋙ G) P U q).hom :=
  Functor.HomologyComposition.comparison F G (Projection.complex U P)
    (Projection.complex U (P ⋙ F))
    (Projection.complex U ((P ⋙ F) ⋙ G))
    (CoefficientChange.complexIso U F P)
    (CoefficientChange.complexIso U G (P ⋙ F))
    (CoefficientChange.complexIso U (F ⋙ G) P) (cochain U F G P) q

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.CoefficientComposition

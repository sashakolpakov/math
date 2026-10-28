import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.CoefficientChange
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.Functor

/-! # Coefficient Change -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.CoefficientChange

noncomputable section

/-! Coefficient change on the literal nonempty ordered Čech complex. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u vA uA vB uB
open OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.Functor.Projection
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  {ι : Type u} [LinearOrder ι] (U : ι → C)
  {A : Type uA} [Category.{vA} A] [Preadditive A] [HasProducts.{u} A]
  {B : Type uB} [Category.{vB} B] [Preadditive B] [HasProducts.{u} B]
  (G : A ⥤ B) [G.Additive] [PreservesLimitsOfSize.{u,u} G]
  (P : Cᵒᵖ ⥤ A)

def complexIso : (G.mapHomologicalComplex (.up ℕ)).obj (Projection.complex U P) ≅ Projection.complex U (P ⋙ G) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => AugmentedCech.CoefficientChange.objectIso U G P (n + 1)) (by
      intro n m h
      obtain rfl : m = n + 1 := h.symm
      change (AugmentedCech.CoefficientChange.objectIso U G P (n + 1)).hom ≫
        (Projection.complex U (P ⋙ G)).d n (n + 1) =
          G.map ((Projection.complex U P).d n (n + 1)) ≫
            (AugmentedCech.CoefficientChange.objectIso U G P (n + 1 + 1)).hom
      simpa only [Projection.complex, CochainComplex.of_d, Projection.differential] using
        (AugmentedCech.CoefficientChange.differential U G P (n + 1)).symm)

theorem naturality {Q : Cᵒᵖ ⥤ A} (f : P ⟶ Q) :
    (G.mapHomologicalComplex (.up ℕ)).map (OrderedCech.Functor.Projection.complexMap U f) ≫ (complexIso U G Q).hom =
      (complexIso U G P).hom ≫ OrderedCech.Functor.Projection.complexMap U (Functor.whiskerRight f G) := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact congrArg (fun a => a.f (n + 1))
    (AugmentedCech.CoefficientChange.naturality U G P f)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.CoefficientChange

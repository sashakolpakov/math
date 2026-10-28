import OAI.NumberTheory.PadicHodge.IntegralComparison.Ordered.SingleGlobalSourceCoefficients
import OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.HomologySquare

/-! # Ordinary Coefficient Projection -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.OrdinaryCoefficientProjection.Ordinary

noncomputable section

/-! The actual ordinary-to-ordered projection commutes with an exact
coefficient change on an arbitrary cover. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u uA vA uB vB
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  {ι : Type u} [LinearOrder ι] (U : ι → C)
  {A : Type uA} [Category.{vA} A] [Abelian A] [HasProducts.{u} A] [HasCoproducts.{0} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasProducts.{u} B] [HasCoproducts.{0} B]
  (G : A ⥤ B) [G.Additive] [G.PreservesHomology] [PreservesLimitsOfSize.{u,u} G]
  (P : Cᵒᵖ ⥤ A)

abbrev ordinaryIso := AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange.CechCoefficientChange.complexIso G (NonemptyCechNerve.nerve U) P

omit [HasCoproducts A] [HasCoproducts B] [G.PreservesHomology] in
theorem cochain :
    (G.mapHomologicalComplex (.up ℕ)).map (Projection.map U P) ≫
      (CoefficientChange.complexIso U G P).hom =
    (ordinaryIso U G P).hom ≫ Projection.map U (P ⋙ G) := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply Pi.hom_ext
  intro (a : Projection.Index (ι := ι) q)
  change (G.map (Projection.mapF U P q) ≫ piComparison G _) ≫
      Projection.projection U (P ⋙ G) q a =
    ((ordinaryIso U G P).hom.f q ≫ Projection.mapF U (P ⋙ G) q) ≫
      Projection.projection U (P ⋙ G) q a
  rw [Category.assoc]
  erw [piComparison_comp_π, ← G.map_comp, Projection.mapF_projection]
  rw [Category.assoc, Projection.mapF_projection]
  rw [AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChangeNaturality.CechCoefficientChangeNaturality.hom_f]
  exact (piComparison_comp_π G _ a.val).symm

omit [HasCoproducts A] [HasCoproducts B] in
theorem homology (q : ℕ) :
    G.map (homologyMap (Projection.map U P) q) ≫
      (Ordered.SingleGlobalSourceCoefficients.coefficientIso G P U q).hom =
    (Functor.HomologySquare.iso G (ordinaryIso U G P) q).hom ≫
      homologyMap (Projection.map U (P ⋙ G)) q :=
  Functor.HomologySquare.naturality G (Projection.map U P)
    (Projection.map U (P ⋙ G)) (ordinaryIso U G P)
    (CoefficientChange.complexIso U G P) (cochain U G P) q

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.OrdinaryCoefficientProjection.Ordinary

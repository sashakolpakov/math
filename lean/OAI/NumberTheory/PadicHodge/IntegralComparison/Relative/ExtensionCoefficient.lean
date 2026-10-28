import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.CoefficientTotal
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.CoefficientTotal
import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.TotalCoefficientSquare

/-! # Extension Coefficient -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.ExtensionCoefficient

noncomputable section

/-! Exact additive coefficient change preserves the original relative
extension, including the sign from the distinguished first chart. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive
open _root_.TopologicalSpace Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u uA vA uB vB
open OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.Intersections OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.ExtensionComponents
variable {X : TopCat.{u}} (U : Opens X)
  {ι : Type u} [LinearOrder ι] (V : ι → Opens X)
  {A : Type uA} [Category.{vA} A] [Abelian A] [HasProducts.{u} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasProducts.{u} B]
  (G : A ⥤ B) [G.Additive] [PreservesLimitsOfSize.{u,u} G]
  (P : (Opens X)ᵒᵖ ⥤ A)

theorem component (n : ℕ) :
    G.map (RelativeCech.ExtensionComponents.component U V P n) ≫
        (AugmentedCech.CoefficientChange.objectIso (RelativeCech.Intersections.cover U V) G P (n+1)).hom =
      (AugmentedCech.CoefficientChange.objectIso V G (RelativeCech.Intersections.presheaf U P) n).hom ≫
        RelativeCech.ExtensionComponents.component U V (P ⋙ G) n := by
  classical
  apply Pi.hom_ext
  intro (a : AugmentedOrdered.Cech.Index (WithBot ι) (n+1))
  have ht : (AugmentedCech.CoefficientChange.objectIso (RelativeCech.Intersections.cover U V) G P (n+1)).hom ≫
      RelativeCech.ExtensionComponents.targetProjection U V (P ⋙ G) a = G.map (RelativeCech.ExtensionComponents.targetProjection U V P a) :=
    piComparison_comp_π G _ a
  have hs (b : AugmentedOrdered.Cech.Index ι n) :
      (AugmentedCech.CoefficientChange.objectIso V G (RelativeCech.Intersections.presheaf U P) n).hom ≫
        RelativeCech.ExtensionComponents.sourceProjection U V (P ⋙ G) b = G.map (RelativeCech.ExtensionComponents.sourceProjection U V P b) :=
    piComparison_comp_π G _ b
  change (_ ≫ _) ≫ RelativeCech.ExtensionComponents.targetProjection U V (P ⋙ G) a =
    (_ ≫ _) ≫ RelativeCech.ExtensionComponents.targetProjection U V (P ⋙ G) a
  rw [Category.assoc, ht, ← G.map_comp, RelativeCech.ExtensionComponents.component_projection,
    Category.assoc, RelativeCech.ExtensionComponents.component_projection]
  by_cases ha : a.val 0 = ⊥
  · simp only [RelativeCech.ExtensionComponents.entry, dite_eq_left ha, Functor.map_zsmul, Functor.map_comp,
      comp_zsmul]
    rw [← Category.assoc, hs]
    rfl
  · simp only [RelativeCech.ExtensionComponents.entry, dite_eq_right ha, Functor.map_zero, comp_zero]

theorem complex :
    (G.mapHomologicalComplex (.up ℕ)).map (RelativeCech.ExtensionDifferential.map U V P) ≫
      (OrderedCech.CoefficientChange.complexIso (RelativeCech.Intersections.cover U V) G P).hom =
    (AugmentedCech.CoefficientChange.complexIso V G (RelativeCech.Intersections.presheaf U P)).hom ≫
      RelativeCech.ExtensionDifferential.map U V (P ⋙ G) := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact component U V G P n

variable [HasCoproducts.{0} A] [HasCoproducts.{0} B]
local instance finiteBiproducts : HasFiniteBiproducts A := HasFiniteBiproducts.of_hasFiniteProducts
variable (K : CochainComplex ((Opens X)ᵒᵖ ⥤ A) ℕ)

omit [HasCoproducts.{0} A] [HasCoproducts.{0} B] in
theorem bicomplex :
    AlgebraicGeometry.Comparison.Betti.TotalAdditiveFunctor.mapBicomplexMap G (RelativeCech.Total.bicomplexMap U V K) ≫
      (OrderedCech.CoefficientTotal.bicomplexIso (RelativeCech.Intersections.cover U V) G K).hom =
    (AugmentedCech.CoefficientTotal.bicomplexIso V G
      (((RelativeCech.Refinement.restriction U).mapHomologicalComplex (.up ℕ)).obj K)).hom ≫
      RelativeCech.Total.bicomplexMap U V (RelativeCech.CoefficientTotal.mapped G K) := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact complex U V G (K.X n)

theorem total :
    (G.mapHomologicalComplex (.up ℕ)).map (RelativeCech.Total.map U V K) ≫
      (OrderedCech.CoefficientTotal.totalIso (RelativeCech.Intersections.cover U V) G K).hom =
    (RelativeCech.CoefficientTotal.iso U V G K).hom ≫
      RelativeCech.Total.map U V (RelativeCech.CoefficientTotal.mapped G K) :=
  Finite.TotalCoefficientSquare.comparison G
    (AugmentedCech.CoefficientTotal.bicomplexIso V G
      (((RelativeCech.Refinement.restriction U).mapHomologicalComplex (.up ℕ)).obj K))
    (OrderedCech.CoefficientTotal.bicomplexIso (RelativeCech.Intersections.cover U V) G K)
    (RelativeCech.Total.bicomplexMap U V K)
    (RelativeCech.Total.bicomplexMap U V (RelativeCech.CoefficientTotal.mapped G K))
    (bicomplex U V G K)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.ExtensionCoefficient

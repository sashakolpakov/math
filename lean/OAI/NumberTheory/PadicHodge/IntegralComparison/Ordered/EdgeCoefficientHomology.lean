import OAI.NumberTheory.PadicHodge.IntegralComparison.Ordered.EdgeCoefficient
import OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.HomologySquare

/-! # Edge Coefficient Homology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Ordered.EdgeCoefficientHomology

noncomputable section

/-! The canonical exact-functor cohomology coordinates preserve the
literal global-section edge of the original ordered Cech total. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex _root_.TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u vA uA vB uB
variable {X : TopCat.{u}} {ι : Type u} [LinearOrder ι] (U : ι → Opens X)
  {A : Type uA} [Category.{vA} A] [Abelian A] [HasProducts.{u} A] [HasCoproducts.{0} A]
  [HasFiniteBiproducts A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasProducts.{u} B] [HasCoproducts.{0} B]
  (G : A ⥤ B) [G.Additive] [PreservesLimitsOfSize.{u,u} G] [G.PreservesHomology]
  (K : CochainComplex ((Opens X)ᵒᵖ ⥤ A) ℕ)

theorem homology (q : ℕ) :
    G.map (homologyMap (Presheaf.OrderedCechEdge.edge U K) q) ≫
      (OrderedCech.CoefficientTotal.homologyIso U G K q).hom =
    (((Presheaf.OrderedCechEdge.sections K).sc q).mapHomologyIso G).inv ≫
      homologyMap (Presheaf.OrderedCechEdge.edge U
        (OrderedCech.CoefficientTotal.mapped G K)) q := by
  have h := Functor.HomologySquare.naturality G
    (Presheaf.OrderedCechEdge.edge U K)
    (Presheaf.OrderedCechEdge.edge U (OrderedCech.CoefficientTotal.mapped G K))
    (Iso.refl _) (OrderedCech.CoefficientTotal.totalIso U G K)
    (by simpa only [Iso.refl_hom, Category.id_comp] using EdgeCoefficient.edge U G K) q
  simp only [Functor.HomologySquare.iso,
    Iso.trans_hom, Iso.symm_hom, homologyMapIso_hom, Iso.refl_hom, homologyMap_id] at h
  erw [Category.comp_id] at h
  exact h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Ordered.EdgeCoefficientHomology

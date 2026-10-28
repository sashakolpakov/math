import OAI.NumberTheory.PadicHodge.GeometricComparison.CechTopConeCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.OrdinaryOrderedEdge
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.TotalProjectionQuasiIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.Ordered.EdgeCoefficientHomology

/-! # Flasque Ordered Global -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FlasqueOrderedGlobal

noncomputable section

/-! The original ordered global edge is an isomorphism for a complex
of flasque module sheaves, on every genuine open cover. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.HomologicalComplex
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
variable (R : Type u) [CommRing R] (X : TopCat.{0})
  {ι : Type} [LinearOrder ι] (U : ι → Opens X)
  (K : CochainComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{max u w} R)) ℕ)

abbrev underlying := GeometricComparison.FlasqueCechGlobal.FlasqueCechGlobalComparison.presheafComplex R X K

theorem quasiIso (hU : iSup U = ⊤)
    (hK : ∀ q, TopCat.Presheaf.IsFlasque (X := X) (K.X q).obj) :
    QuasiIso (IntegralComparison.Presheaf.OrderedCechEdge.edge U (underlying R X K)) := by
  let : QuasiIso (IntegralComparison.Presheaf.OrdinaryOrderedEdge.Ordinary.ordinary U (underlying R X K)) := by
    change QuasiIso (GeometricComparison.FlasqueCechGlobal.FlasqueCechGlobalComparison.map R X U K)
    exact GeometricComparison.FlasqueCechGlobal.FlasqueCechGlobalComparison.quasiIso R X U K hU hK
  let := OrderedCech.TotalProjectionQuasiIso.quasiIso U (underlying R X K)
  rw [← IntegralComparison.Presheaf.OrdinaryOrderedEdge.Ordinary.comparison]
  infer_instance

theorem homology_isIso (hU : iSup U = ⊤)
    (hK : ∀ q, TopCat.Presheaf.IsFlasque (X := X) (K.X q).obj) (q : ℕ) :
    IsIso (homologyMap (IntegralComparison.Presheaf.OrderedCechEdge.edge U (underlying R X K)) q) := by
  let := quasiIso R X U K hU hK
  infer_instance

end

namespace EdgeCoefficient
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u vA uA vB uB
variable {X : TopCat.{u}} {ι : Type u} [LinearOrder ι] (U : ι → Opens X)
  {A : Type uA} [Category.{vA} A] [Abelian A] [HasProducts.{u} A] [HasCoproducts.{0} A]
  [HasFiniteBiproducts A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasProducts.{u} B] [HasCoproducts.{0} B]
  (G : A ⥤ B) [G.Additive] [PreservesLimitsOfSize.{u,u} G] [G.PreservesHomology]
  (K : CochainComplex ((Opens X)ᵒᵖ ⥤ A) ℕ) (q : ℕ)
  [IsIso (homologyMap (IntegralComparison.Presheaf.OrderedCechEdge.edge U K) q)]

theorem homology_isIso :
    IsIso (homologyMap (IntegralComparison.Presheaf.OrderedCechEdge.edge U
      (OrderedCech.CoefficientTotal.mapped G K)) q) := by
  have he : homologyMap (IntegralComparison.Presheaf.OrderedCechEdge.edge U
      (OrderedCech.CoefficientTotal.mapped G K)) q =
      (((IntegralComparison.Presheaf.OrderedCechEdge.sections K).sc q).mapHomologyIso G).hom ≫
        G.map (homologyMap (IntegralComparison.Presheaf.OrderedCechEdge.edge U K) q) ≫
        (OrderedCech.CoefficientTotal.homologyIso U G K q).hom := by
    apply (cancel_epi (((IntegralComparison.Presheaf.OrderedCechEdge.sections K).sc q).mapHomologyIso G).inv).mp
    simp only [Iso.inv_hom_id_assoc]
    exact (Ordered.EdgeCoefficientHomology.homology U G K q).symm
  rw [he]
  infer_instance

end EdgeCoefficient

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FlasqueOrderedGlobal

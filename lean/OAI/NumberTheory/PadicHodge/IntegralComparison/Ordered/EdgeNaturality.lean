import OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.OrderedCechEdge

/-! # Edge Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Ordered.EdgeNaturality

noncomputable section

/-! Naturality of the literal ordered Čech global edge in its
coefficient complex. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex _root_.TopologicalSpace Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
variable {X : TopCat.{u}} {ι : Type u} [LinearOrder ι] (U : ι → Opens X)
  {D : Type v} [Category.{w} D] [Preadditive D] [HasProducts.{u} D] [HasCoproducts.{0} D]
  {K L : CochainComplex ((Opens X)ᵒᵖ ⥤ D) ℕ} (f : K ⟶ L)

def sectionsMap := ((((evaluation (Opens X)ᵒᵖ D).obj (op (⊤ : Opens X))).mapHomologicalComplex
  (.up ℕ)).map f)
def totalMap := HomologicalComplex₂.total.map
  (((OrderedCech.Functor.Projection.functor U).mapHomologicalComplex (.up ℕ)).map f) (.up ℕ)

theorem naturality :
    Presheaf.OrderedCechEdge.edge U K ≫ totalMap U f =
      sectionsMap f ≫ Presheaf.OrderedCechEdge.edge U L := by
  exact BicomplexHorizontalEdge.naturality
    (Presheaf.OrderedCechEdge.bicomplex U K) (Presheaf.OrderedCechEdge.sections K)
    (fun q => Presheaf.OrderedCechEdge.augmentation U (K.X q))
    (fun q q' _ => Presheaf.OrderedCechEdge.augmentation_comm U K q q')
    (Presheaf.OrderedCechEdge.augmentation_cocycle U K)
    (Presheaf.OrderedCechEdge.bicomplex U L) (Presheaf.OrderedCechEdge.sections L)
    (fun q => Presheaf.OrderedCechEdge.augmentation U (L.X q))
    (fun q q' _ => Presheaf.OrderedCechEdge.augmentation_comm U L q q')
    (Presheaf.OrderedCechEdge.augmentation_cocycle U L)
    (((OrderedCech.Functor.Projection.functor U).mapHomologicalComplex (.up ℕ)).map f)
    (sectionsMap f) (fun q => (Presheaf.OrderedCechEdge.augmentation_naturality U (K.X q) (f.f q)).symm)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Ordered.EdgeNaturality

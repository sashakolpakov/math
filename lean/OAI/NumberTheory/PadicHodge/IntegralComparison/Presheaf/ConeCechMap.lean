import OAI.NumberTheory.PadicHodge.IntegralComparison.Global.SectionCechEdge

/-! # Cone Cech Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.ConeCechMap

noncomputable section

/-! A literal constant-presheaf cone maps into the native Čech total.
Its product formula uses the actual cochain augmentation in every degree. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  (R : Type u) [CommRing R] {ι : Type} [Finite ι] (F : ι → C)
  (M : CochainComplex (ModuleCat.{u} R) ℕ)
  (P : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} R) ℕ)
  (a : ((Functor.const Cᵒᵖ).mapHomologicalComplex (.up ℕ)).obj M ⟶ P)

def cone : (Functor.const Cᵒᵖ).obj M ⟶ Global.SectionCechEdge.diagram R P where
  app V :=
    { f q := (a.f q).app V
      comm' i j _ := congrArg (fun f => f.app V) (a.comm i j) }
  naturality V W α := by
    apply HomologicalComplex.Hom.ext
    funext q
    exact (a.f q).naturality α

def map : M ⟶ TotalCup.CechProduct.total (NonemptyCechNerve.nerve F)
    (Cech.ComplexDiagramCoordinates.complex (Global.SectionCechEdge.diagram R P)) :=
  GeometricComparison.CechCone.Total.CechConeTotal.augmentation F (Global.SectionCechEdge.diagram R P) M (cone R M P a) ≫
    (Cech.ComplexDiagramCoordinates.totalIso F (Global.SectionCechEdge.diagram R P)).hom

variable (μ : ∀ i j V, (P.X i).obj V →ₗ[R] (P.X j).obj V →ₗ[R] (P.X (i+j)).obj V)
  (σ : ∀ i j, M.X i →ₗ[R] M.X j →ₗ[R] M.X (i+j))
  (ha : ∀ i j V x y, (a.f (i+j)).app V (σ i j x y) =
    μ i j V ((a.f i).app V x) ((a.f j).app V y))

abbrev map_cup := Cech.DiagramAugmentationGradedProduct.augmentation_product R F
  (Global.SectionCechEdge.diagram R P) M (cone R M P a) μ σ ha

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.ConeCechMap

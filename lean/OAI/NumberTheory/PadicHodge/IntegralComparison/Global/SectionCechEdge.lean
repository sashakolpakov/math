import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.DiagramAugmentationGradedProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.ExhaustiveSectionNaturality

/-! # Section Cech Edge -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Global.SectionCechEdge

noncomputable section

/-! Evaluation of genuine global presheaf sections gives the original
Čech augmentation of any coefficient complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  (R : Type u) [CommRing R] {ι : Type} [Finite ι] (F : ι → C)
  (P : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} R) ℕ)

abbrev globalFunctor : (Cᵒᵖ ⥤ ModuleCat.{u} R) ⥤ ModuleCat.{u} R :=
  ExhaustiveSectionNaturality.globalSectionsFunctor R (ModuleCat.of R R)

def globalComplex : CochainComplex (ModuleCat.{u} R) ℕ :=
  ((globalFunctor (C := C) R).mapHomologicalComplex (.up ℕ)).obj P

def diagram : Cᵒᵖ ⥤ CochainComplex (ModuleCat.{u} R) ℕ where
  obj V := (((evaluation Cᵒᵖ (ModuleCat.{u} R)).obj V).mapHomologicalComplex (.up ℕ)).obj P
  map α := (NatTrans.mapHomologicalComplex
    ((evaluation Cᵒᵖ (ModuleCat.{u} R)).map α) (.up ℕ)).app P

def evaluate (q : ℕ) (V : Cᵒᵖ) : (globalComplex R P).X q ⟶ (P.X q).obj V :=
  ModuleCat.ofHom
    { toFun := fun s => s.app V (1 : R)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

def cone : (Functor.const Cᵒᵖ).obj (globalComplex R P) ⟶ diagram R P where
  app V :=
    { f q := evaluate R P q V
      comm' i j _ := rfl }
  naturality V W α := by
    apply HomologicalComplex.Hom.ext
    funext q
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    exact ConcreteCategory.congr_hom (s.naturality α) (1 : R)

def edge : globalComplex R P ⟶
    Presheaf.TotalCup.CechProduct.total (NonemptyCechNerve.nerve F)
      (Cech.ComplexDiagramCoordinates.complex (diagram R P)) :=
  GeometricComparison.CechCone.Total.CechConeTotal.augmentation F (diagram R P) (globalComplex R P) (cone R P) ≫
    (Cech.ComplexDiagramCoordinates.totalIso F (diagram R P)).hom

theorem component (q : ℕ) : (edge R F P).f q =
    Cech.DiagramAugmentationCoordinates.Complex.restriction F (diagram R P) (globalComplex R P) (cone R P) q ≫
      (CechCoefficient.Total.bicomplex (NonemptyCechNerve.nerve F)
        (Cech.ComplexDiagramCoordinates.complex (diagram R P))).ιTotal (.up ℕ) q 0 q rfl :=
  Cech.DiagramAugmentationCoordinates.Complex.augmentation_component F (diagram R P)
    (globalComplex R P) (cone R P) q

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Global.SectionCechEdge

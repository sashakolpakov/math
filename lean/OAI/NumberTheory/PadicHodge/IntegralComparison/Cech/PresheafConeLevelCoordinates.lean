import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.PresheafDiagramCone
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalFunctorSquare

/-! # Presheaf Cone Level Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.PresheafConeLevelCoordinates

noncomputable section

/-! The original pointwise presheaf Čech cone is the canonical
coefficient-transported Čech map in the original total coordinates. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v d e r t w z

section Identity

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {A : Type w} [Category.{z} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  {ι : Type} [Finite ι] (U : ι → C) (Q : Cᵒᵖ ⥤ CochainComplex A ℕ)

theorem coefficient_identity :
    (GeometricComparison.CechCone.TotalCoefficient.CechConeTotalCoefficient.totalIso (𝟭 A) U Q).hom =
      𝟙 (GeometricComparison.CechCone.Total.CechConeTotal.total U Q) := by
  have h := GeometricComparison.CechCone.CoefficientComposition.CechConeCoefficientComposition.total (𝟭 A) (𝟭 A) U Q
  change (GeometricComparison.CechCone.TotalCoefficient.CechConeTotalCoefficient.totalIso (𝟭 A) U Q).hom =
    (GeometricComparison.CechCone.TotalCoefficient.CechConeTotalCoefficient.totalIso (𝟭 A) U Q).hom ≫
      (GeometricComparison.CechCone.TotalCoefficient.CechConeTotalCoefficient.totalIso (𝟭 A) U Q).hom at h
  apply (cancel_epi (GeometricComparison.CechCone.TotalCoefficient.CechConeTotalCoefficient.totalIso (𝟭 A) U Q).hom).mp
  exact h.symm.trans (Category.comp_id _).symm

end Identity

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {D : Type d} [Category.{e} D] (R : Type r) [CommRing R]
  {ι : Type} [Finite ι] (U : ι → C)
  (Q : Cᵒᵖ ⥤ CochainComplex (ModuleCat.{t} R) ℕ)
  (P : Cᵒᵖ ⥤ CochainComplex (Dᵒᵖ ⥤ ModuleCat.{t} R) ℕ)
  (a : Q ⋙ (Functor.const Dᵒᵖ).mapHomologicalComplex (.up ℕ) ⟶ P)

open OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.DiagramSectionCoordinates OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.PresheafDiagramCone

def evaluationUnit (T : Dᵒᵖ) :
    𝟭 (ModuleCat.{t} R) ⟶ Functor.const Dᵒᵖ ⋙ DiagramSectionCoordinates.evaluation R T where
  app _ := 𝟙 _
  naturality _ _ _ := by simp

theorem evaluationUnit_complex (T : Dᵒᵖ) (K : CochainComplex (ModuleCat.{t} R) ℕ) :
    ((evaluationUnit R T).mapHomologicalComplex (.up ℕ)).app K = 𝟙 K := by
  apply HomologicalComplex.Hom.ext
  funext q
  rfl

omit [HasBinaryProducts C] in
theorem evaluation_diagram (T : Dᵒᵖ) :
    GeometricComparison.CechCone.TotalFunctorSquare.CechConeTotalFunctorSquare.diagramMap (Functor.const Dᵒᵖ)
      (𝟭 (ModuleCat.{t} R)) (DiagramSectionCoordinates.evaluation R T) Q P a (evaluationUnit R T) =
    PresheafDiagramCone.localMap R Q P a T := by
  apply NatTrans.ext
  funext V
  apply HomologicalComplex.Hom.ext
  funext q
  exact Category.id_comp _

theorem evaluated_level (T : Dᵒᵖ) :
    ((DiagramSectionCoordinates.evaluation R T).mapHomologicalComplex (.up ℕ)).map
        (GeometricComparison.CechCone.TotalLevelMap.CechConeTotalLevelMap.map (Functor.const Dᵒᵖ) U Q P a) ≫
      (GeometricComparison.CechCone.TotalCoefficient.CechConeTotalCoefficient.totalIso (DiagramSectionCoordinates.evaluation R T) U P).hom =
    (GeometricComparison.CechCone.TotalFunctor.CechConeTotalFunctor.functor U).map (PresheafDiagramCone.localMap R Q P a T) := by
  have h := GeometricComparison.CechCone.TotalFunctorSquare.CechConeTotalFunctorSquare.natural (Functor.const Dᵒᵖ)
    (𝟭 (ModuleCat.{t} R)) (DiagramSectionCoordinates.evaluation R T) U Q P a (evaluationUnit R T)
  simp only [GeometricComparison.CechCone.TotalFunctorSquare.CechConeTotalFunctorSquare.map, evaluationUnit_complex,
    coefficient_identity, evaluation_diagram] at h
  erw [Category.id_comp, Category.id_comp] at h
  exact h

theorem local_coordinates (T : Dᵒᵖ) :
    (ComplexDiagramCoordinates.totalIso U Q).hom ≫ PresheafDiagramCone.localTotalMap R U Q P a T =
    ((DiagramSectionCoordinates.evaluation R T).mapHomologicalComplex (.up ℕ)).map
      (GeometricComparison.CechCone.TotalLevelMap.CechConeTotalLevelMap.map (Functor.const Dᵒᵖ) U Q P a) := by
  apply (cancel_mono (DiagramSectionCoordinates.totalIso R U P T).hom).mp
  simp only [PresheafDiagramCone.localTotalMap, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change (ComplexDiagramCoordinates.totalIso U Q).hom ≫
      ComplexDiagramNaturality.Coordinates.totalMap U (PresheafDiagramCone.localMap R Q P a T) =
    ((DiagramSectionCoordinates.evaluation R T).mapHomologicalComplex (.up ℕ)).map
        (GeometricComparison.CechCone.TotalLevelMap.CechConeTotalLevelMap.map (Functor.const Dᵒᵖ) U Q P a) ≫
      (GeometricComparison.CechCone.TotalCoefficient.CechConeTotalCoefficient.totalIso (DiagramSectionCoordinates.evaluation R T) U P).hom ≫
        (ComplexDiagramCoordinates.totalIso U (DiagramSectionCoordinates.diagram R P T)).hom
  rw [← Category.assoc, evaluated_level]
  exact (ComplexDiagramNaturality.Coordinates.total_natural U (PresheafDiagramCone.localMap R Q P a T)).symm

theorem map_eq :
    ((Functor.const Dᵒᵖ).mapHomologicalComplex (.up ℕ)).map
        (ComplexDiagramCoordinates.totalIso U Q).hom ≫
      PresheafDiagramCone.map R U Q P a =
    GeometricComparison.CechCone.TotalLevelMap.CechConeTotalLevelMap.map (Functor.const Dᵒᵖ) U Q P a := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply NatTrans.ext
  funext T
  exact congrArg (fun f => f.f q) (local_coordinates R U Q P a T)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.PresheafConeLevelCoordinates

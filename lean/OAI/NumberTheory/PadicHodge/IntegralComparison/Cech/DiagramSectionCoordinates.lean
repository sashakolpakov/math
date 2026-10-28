import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ComplexDiagramNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.CoefficientTransformation
import OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.TotalCup

/-! # Diagram Section Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.DiagramSectionCoordinates

noncomputable section

/-! Pointwise coordinates for the original presheaf-valued Čech total,
natural in the actual section restriction maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v d e r t
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {D : Type d} [Category.{e} D] (R : Type r) [CommRing R]
  {ι : Type} [Finite ι] (U : ι → C)
  (P : Cᵒᵖ ⥤ CochainComplex (Dᵒᵖ ⥤ ModuleCat.{t} R) ℕ)

local notation "N" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve U

abbrev evaluation (V : Dᵒᵖ) : (Dᵒᵖ ⥤ ModuleCat.{t} R) ⥤ ModuleCat.{t} R :=
  (CategoryTheory.evaluation Dᵒᵖ (ModuleCat.{t} R)).obj V

def diagram (V : Dᵒᵖ) := GeometricComparison.CechCone.TotalCoefficient.CechConeTotalCoefficient.mapped (DiagramSectionCoordinates.evaluation R V) P

def complex (V : Dᵒᵖ) := ComplexDiagramCoordinates.complex (diagram R P V)

def totalIso (V : Dᵒᵖ) :
    ((DiagramSectionCoordinates.evaluation R V).mapHomologicalComplex (.up ℕ)).obj (GeometricComparison.CechCone.Total.CechConeTotal.total U P) ≅
      Presheaf.TotalCup.CechProduct.total.{u,v,0,t,r} N (complex R P V) :=
  GeometricComparison.CechCone.TotalCoefficient.CechConeTotalCoefficient.totalIso (DiagramSectionCoordinates.evaluation R V) U P ≪≫
    ComplexDiagramCoordinates.totalIso U (diagram R P V)

def evaluationMap {V W : Dᵒᵖ} (α : V ⟶ W) : DiagramSectionCoordinates.evaluation R V ⟶ DiagramSectionCoordinates.evaluation R W :=
  (CategoryTheory.evaluation Dᵒᵖ (ModuleCat.{t} R)).map α

def diagramMap {V W : Dᵒᵖ} (α : V ⟶ W) : diagram R P V ⟶ diagram R P W :=
  Functor.whiskerLeft P ((evaluationMap R α).mapHomologicalComplex (.up ℕ))

def complexMap {V W : Dᵒᵖ} (α : V ⟶ W) : complex R P V ⟶ complex R P W :=
  ComplexDiagramNaturality.Coordinates.complexMap (diagramMap R P α)

def totalMap {V W : Dᵒᵖ} (α : V ⟶ W) :=
  ComplexDiagramNaturality.Coordinates.totalMap U (diagramMap R P α)

theorem total_natural {V W : Dᵒᵖ} (α : V ⟶ W) :
    ((evaluationMap R α).mapHomologicalComplex (.up ℕ)).app (GeometricComparison.CechCone.Total.CechConeTotal.total U P) ≫
      (totalIso R U P W).hom = (totalIso R U P V).hom ≫ totalMap R U P α :=
  GeometricComparison.ExactHomology.ExactHomologyComparison.compose _ _ _ _ _ _ _
    (GeometricComparison.CechCone.CoefficientTransformation.CechConeCoefficientTransformation.total (DiagramSectionCoordinates.evaluation R V) (DiagramSectionCoordinates.evaluation R W)
      (evaluationMap R α) U P)
    (ComplexDiagramNaturality.Coordinates.total_natural U (diagramMap R P α))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.DiagramSectionCoordinates

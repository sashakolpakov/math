import OAI.AlgebraicGeometry.PELModuli.CMPoints.ComponentFactorData
import OAI.AlgebraicGeometry.PELModuli.CMPoints.ScalarFactorPair
import OAI.AlgebraicGeometry.PELModuli.CMPoints.ComplexDiagramSpreading

/-! # Component Diagram -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints

noncomputable section

/-! Construct and spread the finite auxiliary CM diagram for each
original component. Its objects include the literal PEL fiber and the
three CM factors; its arrows include all splitting maps and basis actions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  (M : Models.RankThreePELModel E K) {hM : M.HasPrescribedBallPeriods}
  {a : M.Family} {t : Fin (M.componentCount a)}

def Models.RankThreePELModel.CMComponentFactorData.diagram (C : M.CMComponentFactorData hM a t) : ArithmeticComplexDiagrams.FiniteComplexAbelianDiagram :=
  ScalarFactorPair.ScalarFactorDiagram.diagram
    ((M.componentPolarized a t).abelian.pullback
      (Spec.map (CommRingCat.ofHom C.field.subtype) ≫ C.point))
    (fun i => (C.factor i).abelianScheme) C.splitting
    (Module.finBasis ℤ (NumberField.RingOfIntegers E)) (fun i => (C.factor i).integralAction)

def Models.RankThreePELModel.CMComponentFactorData.diagramModels (C : M.CMComponentFactorData hM a t) :
    ∀ i, AbelianArithmeticModels.AbelianNumberFieldModel ((C.diagram M).abelian i) :=
  ScalarFactorPair.ScalarFactorDiagram.models _ _ C.splitting
    (Module.finBasis ℤ (NumberField.RingOfIntegers E)) (fun i => (C.factor i).integralAction)
    (C.originalModel M) C.factorModel

theorem Models.RankThreePELModel.exists_spread_CM_component_diagram
    [IsGalois ℚ E]
    (hHilb : IntegralModel.Presentations.Hilbert.HilbertHomInput.{0}) (hEnd : IntegralModel.Presentations.Hilbert.EndomorphismEquationsInput.{0})
    (hCMAbelianVarietyA : Descent.AbelianInput) (hCMAbelianVarietyM : Descent.ModuliInput)
    (hM : M.HasPrescribedBallPeriods) (a : M.Family) (t : Fin (M.componentCount a)) :
    ∃ C : M.CMComponentFactorData hM a t,
      ∃ Q : ArithmeticComplexDiagrams.ArithmeticComplexDiagramModel (C.diagram M) (C.diagramModels M),
        ∃ R : AbelianDiagramSpreading.SpreadFiniteAbelianDiagram Q.diagram Q.embedding,
          M.arithmetic.denominator ∣ R.base.denominator := by
  obtain ⟨C⟩ := M.exists_CM_component_factor_data hCMAbelianVarietyA hCMAbelianVarietyM hM a t
  obtain ⟨Q, R, hR⟩ := ComplexDiagramSpreading.exists_spread_complex_abelian_diagram hHilb hEnd (C.diagram M)
    (C.diagramModels M) M.arithmetic.denominator M.arithmetic.denominator_ne_zero
  exact ⟨C, Q, R, hR⟩

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints
